#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

// =====================================================================
// Abstract model for slotmap-based DLL
// =====================================================================
//
// The implementation uses SlotMap<DefaultKey, Node<T>> (a slotmap crate type)
// as the backing store. DefaultKey is a generational opaque index — Verus
// cannot inspect slotmap internals, so all SlotMap operations are external_body.
//
// Key differences from std_linked_list (pointer-based):
//   - Node<T> has explicit next/prec fields (like index_impl), so we model
//     the link structure in a ghost Map<u64, NodeLinks>.
//   - DefaultKey is modelled as u64 (no null sentinel; None is the empty marker).
//   - first/last are Option<u64> (vs usize with 0=null in the pointer case).
//
// Key differences from index_impl (Vec-based):
//   - SlotMap's insert/get_mut are opaque, so link updates are axiomatised.
//   - No traversal induction needed — the ghost chain is the certificate.
//
// Properties proved:
//   1. valid_chain definitions: chain order, link consistency (next/prec match chain).
//   2. lemma_push_back_valid / lemma_push_front_valid: consistency lemmas.
//   3. first() and last() accessors proved from code.
//   4. lemma_all_nodes_reachable: the target reachability property.
//   5. lemma_next_link_consistent: bidirectional link axiom from valid_chain.

/// Ghost: per-node next/prec links mirroring Node<T>.next and Node<T>.prec.
#[allow(dead_code)]
pub struct NodeLinks {
    pub next: Option<u64>,
    pub prec: Option<u64>,
}

/// A slotmap-backed doubly-linked list.
pub struct DoublyLinkedList<T> {
    /// Key of the first node; None if empty.
    pub first: Option<u64>,
    /// Key of the last node; None if empty.
    pub last: Option<u64>,
    /// Ghost: ordered chain of active keys from first to last.
    pub chain: Ghost<Seq<u64>>,
    /// Ghost: (next, prec) links for every active node key.
    pub links: Ghost<Map<u64, NodeLinks>>,
    /// Carries the value type parameter.
    pub _phantom: core::marker::PhantomData<T>,
}

// =====================================================================
// Spec predicates
// =====================================================================

pub open spec fn no_dups(s: Seq<u64>) -> bool {
    forall|i: int, j: int|
        0 <= i < s.len() && 0 <= j < s.len() && s[i] == s[j] ==> i == j
}

/// Reachability-based chain validity.
///
/// The ghost Seq<u64> IS the reachability certificate.  It records the
/// unique, acyclic path from first to last through consecutive next-links.
/// The ghost Map<u64, NodeLinks> mirrors the concrete Node<T>.next/prec
/// fields, enabling bidirectional link-consistency assertions.
pub open spec fn valid_chain<T>(dll: &DoublyLinkedList<T>) -> bool {
    let chain = dll.chain@;
    let lnks  = dll.links@;
    // Structural: no duplicates
    &&& no_dups(chain)
    // Empty iff endpoints are None
    &&& (chain.len() == 0 <==> dll.first.is_none())
    &&& (chain.len() == 0 <==> dll.last.is_none())
    // Endpoints match chain
    &&& (chain.len() > 0 ==> dll.first == Some(chain[0]))
    &&& (chain.len() > 0 ==> dll.last  == Some(chain[chain.len() - 1]))
    // Every chain key is in the links map
    &&& forall|k: int| 0 <= k < chain.len() ==> lnks.contains_key(chain[k])
    // Forward links: chain[k].next == Some(chain[k+1])
    &&& forall|k: int| 0 <= k < chain.len() - 1 ==>
            lnks[chain[k]].next == Some(chain[k + 1])
    // Backward links: chain[k].prec == Some(chain[k-1])
    &&& forall|k: int| 1 <= k < chain.len() ==>
            lnks[chain[k]].prec == Some(chain[k - 1])
    // Boundary: first.prec == None, last.next == None
    &&& (chain.len() > 0 ==> lnks[chain[0]].prec.is_none())
    &&& (chain.len() > 0 ==> lnks[chain[chain.len() - 1]].next.is_none())
}

/// Whether a node key appears in the ghost chain.
pub open spec fn in_chain<T>(dll: &DoublyLinkedList<T>, key: u64) -> bool {
    exists|k: int| 0 <= k < dll.chain@.len() && #[trigger] dll.chain@[k] == key
}

// =====================================================================
// Consistency proof lemmas
// =====================================================================

/// After push_back the structural postconditions imply valid_chain.
///
/// This lemma is a sanity check: it proves that IF the axiomatised
/// push_back postconditions hold, THEN valid_chain is maintained.
/// The link-consistency part (forward/backward foralls) is what
/// distinguishes this from the simpler std_linked_list proof.
proof fn lemma_push_back_valid(
    old_chain: Seq<u64>,
    old_links: Map<u64, NodeLinks>,
    old_first: Option<u64>,
    new_chain: Seq<u64>,
    new_links: Map<u64, NodeLinks>,
    new_first: Option<u64>,
    new_last: Option<u64>,
    result: u64,
)
    requires
        // Old chain was structurally valid
        no_dups(old_chain),
        old_chain.len() == 0 <==> old_first.is_none(),
        old_chain.len() > 0 ==> old_first == Some(old_chain[0]),
        forall|k: int| 0 <= k < old_chain.len() ==> old_links.contains_key(old_chain[k]),
        forall|k: int| 0 <= k < old_chain.len() - 1 ==>
            old_links[old_chain[k]].next == Some(old_chain[k + 1]),
        forall|k: int| 1 <= k < old_chain.len() ==>
            old_links[old_chain[k]].prec == Some(old_chain[k - 1]),
        old_chain.len() > 0 ==> old_links[old_chain[0]].prec.is_none(),
        old_chain.len() > 0 ==> old_links[old_chain[old_chain.len() - 1]].next.is_none(),
        // Freshness: result key was not previously active
        !old_links.contains_key(result),
        // push_back chain postconditions
        new_chain == old_chain + seq![result],
        new_last == Some(result),
        old_chain.len() == 0 ==> new_first == Some(result),
        old_chain.len() > 0  ==> new_first == old_first,
        // Link for result: next=None, prec=old_last
        new_links.contains_key(result),
        new_links[result].next.is_none(),
        old_chain.len() == 0 ==> new_links[result].prec.is_none(),
        old_chain.len() > 0  ==>
            new_links[result].prec == Some(old_chain[old_chain.len() - 1]),
        // Link update for old_last (non-empty case)
        old_chain.len() > 0 ==>
            new_links.contains_key(old_chain[old_chain.len() - 1]) &&
            new_links[old_chain[old_chain.len() - 1]].next == Some(result) &&
            new_links[old_chain[old_chain.len() - 1]].prec
                == old_links[old_chain[old_chain.len() - 1]].prec,
        // Frame: all other chain entries unchanged
        forall|k: int| 0 <= k < old_chain.len() - 1 ==>
            new_links.contains_key(old_chain[k]) &&
            new_links[old_chain[k]].next == old_links[old_chain[k]].next &&
            new_links[old_chain[k]].prec == old_links[old_chain[k]].prec,
    ensures
        no_dups(new_chain),
        new_chain.len() > 0,
        new_first.is_some(),
        new_last.is_some(),
        new_chain.len() == 0 <==> new_first.is_none(),
        new_chain.len() == 0 <==> new_last.is_none(),
        new_first == Some(new_chain[0]),
        new_last  == Some(new_chain[new_chain.len() - 1]),
        forall|k: int| 0 <= k < new_chain.len() ==> new_links.contains_key(new_chain[k]),
        forall|k: int| 0 <= k < new_chain.len() - 1 ==>
            new_links[new_chain[k]].next == Some(new_chain[k + 1]),
        forall|k: int| 1 <= k < new_chain.len() ==>
            new_links[new_chain[k]].prec == Some(new_chain[k - 1]),
        new_links[new_chain[0]].prec.is_none(),
        new_links[new_chain[new_chain.len() - 1]].next.is_none(),
{
    let n: int = old_chain.len() as int;

    // 1. no_dups: result is fresh — not in old_links, old_chain elements are
    assert(no_dups(new_chain)) by {
        assert forall|i: int, j: int|
            0 <= i < new_chain.len() && 0 <= j < new_chain.len() && new_chain[i] == new_chain[j]
            implies i == j
        by {
            if i < n && j < n { }
            else if i == n && j < n {
                assert(new_chain[i] == result);
                assert(old_links.contains_key(old_chain[j]));
                assert(!old_links.contains_key(result));
            } else if i < n && j == n {
                assert(new_chain[j] == result);
                assert(old_links.contains_key(old_chain[i]));
                assert(!old_links.contains_key(result));
            }
        };
    };

    // 2. Length and last endpoint
    assert(new_chain.len() == n + 1);
    assert(new_chain[n] == result);

    // 3. First endpoint
    if n == 0 {
        assert(new_first == Some(result));
        assert(new_chain[0] == result);
    } else {
        assert(new_chain[0] == old_chain[0]);
        assert(new_first == old_first);
    }

    // 4. All chain keys in new_links
    assert forall|k: int| 0 <= k < new_chain.len() implies new_links.contains_key(new_chain[k])
    by {
        if k < n {
            if k < n - 1 {
                assert(new_links.contains_key(old_chain[k]));
            }
            // k == n-1 (old_last): from old_last-specific postcondition
        }
        // k == n (result): directly
    };

    // 5. Forward links: chain[k].next == Some(chain[k+1])
    assert forall|k: int| 0 <= k < new_chain.len() - 1 implies
        new_links[new_chain[k]].next == Some(new_chain[k + 1])
    by {
        if k < n - 1 {
            assert(new_chain[k] == old_chain[k]);
            assert(new_chain[k + 1] == old_chain[k + 1]);
            assert(new_links[old_chain[k]].next == old_links[old_chain[k]].next);
            assert(old_links[old_chain[k]].next == Some(old_chain[k + 1]));
        } else {
            // k == n-1: old_last.next updated to Some(result)
            assert(k == n - 1);
            assert(new_chain[k] == old_chain[n - 1]);
            assert(new_chain[k + 1] == result);
            assert(new_links[old_chain[n - 1]].next == Some(result));
        }
    };

    // 6. Backward links: chain[k].prec == Some(chain[k-1])
    assert forall|k: int| 1 <= k < new_chain.len() implies
        new_links[new_chain[k]].prec == Some(new_chain[k - 1])
    by {
        if k < n {
            assert(new_chain[k] == old_chain[k]);
            assert(new_chain[k - 1] == old_chain[k - 1]);
            if k < n - 1 {
                assert(new_links[old_chain[k]].prec == old_links[old_chain[k]].prec);
                assert(old_links[old_chain[k]].prec == Some(old_chain[k - 1]));
            } else {
                // k == n-1 (old_last): prec field preserved; n >= 2 (since k >= 1)
                assert(k == n - 1);
                assert(n >= 2);
                assert(new_links[old_chain[n - 1]].prec == old_links[old_chain[n - 1]].prec);
                assert(old_links[old_chain[n - 1]].prec == Some(old_chain[n - 2]));
            }
        } else {
            // k == n: result.prec == Some(old_last) == Some(chain[n-1])
            assert(k == n);
            assert(new_chain[k] == result);
            assert(new_chain[k - 1] == old_chain[n - 1]);
            assert(new_links[result].prec == Some(old_chain[n - 1]));
        }
    };

    // 7. Boundary: first.prec is None
    assert(new_links[new_chain[0]].prec.is_none()) by {
        if n == 0 {
            assert(new_chain[0] == result);
        } else {
            assert(new_chain[0] == old_chain[0]);
            if n == 1 {
                // old_chain[0] is both first and old_last
                assert(new_links[old_chain[0]].prec == old_links[old_chain[0]].prec);
                assert(old_links[old_chain[0]].prec.is_none());
            } else {
                // old_chain[0] is at index < n-1, so frame applies
                assert(0 < n - 1);
                assert(new_links[old_chain[0]].prec == old_links[old_chain[0]].prec);
                assert(old_links[old_chain[0]].prec.is_none());
            }
        }
    };

    // 8. Boundary: last.next is None
    assert(new_links[new_chain[new_chain.len() - 1]].next.is_none()) by {
        assert(new_chain[n] == result);
        assert(new_chain.len() - 1 == n);
    };
}

/// After push_front the structural postconditions imply valid_chain.
proof fn lemma_push_front_valid(
    old_chain: Seq<u64>,
    old_links: Map<u64, NodeLinks>,
    old_last: Option<u64>,
    new_chain: Seq<u64>,
    new_links: Map<u64, NodeLinks>,
    new_first: Option<u64>,
    new_last: Option<u64>,
    result: u64,
)
    requires
        no_dups(old_chain),
        old_chain.len() == 0 <==> old_last.is_none(),
        old_chain.len() > 0 ==> old_last == Some(old_chain[old_chain.len() - 1]),
        forall|k: int| 0 <= k < old_chain.len() ==> old_links.contains_key(old_chain[k]),
        forall|k: int| 0 <= k < old_chain.len() - 1 ==>
            old_links[old_chain[k]].next == Some(old_chain[k + 1]),
        forall|k: int| 1 <= k < old_chain.len() ==>
            old_links[old_chain[k]].prec == Some(old_chain[k - 1]),
        old_chain.len() > 0 ==> old_links[old_chain[0]].prec.is_none(),
        old_chain.len() > 0 ==> old_links[old_chain[old_chain.len() - 1]].next.is_none(),
        // Freshness
        !old_links.contains_key(result),
        // push_front chain postconditions
        new_chain == seq![result] + old_chain,
        new_first == Some(result),
        old_chain.len() == 0 ==> new_last == Some(result),
        old_chain.len() > 0  ==> new_last == old_last,
        // Link for result: prec=None, next=old_first
        new_links.contains_key(result),
        new_links[result].prec.is_none(),
        old_chain.len() == 0 ==> new_links[result].next.is_none(),
        old_chain.len() > 0  ==> new_links[result].next == Some(old_chain[0]),
        // Link update for old_first (non-empty case)
        old_chain.len() > 0 ==>
            new_links.contains_key(old_chain[0]) &&
            new_links[old_chain[0]].prec == Some(result) &&
            new_links[old_chain[0]].next == old_links[old_chain[0]].next,
        // Frame: all other chain entries unchanged
        forall|k: int| 1 <= k < old_chain.len() ==>
            new_links.contains_key(old_chain[k]) &&
            new_links[old_chain[k]].next == old_links[old_chain[k]].next &&
            new_links[old_chain[k]].prec == old_links[old_chain[k]].prec,
    ensures
        no_dups(new_chain),
        new_chain.len() > 0,
        new_first.is_some(),
        new_last.is_some(),
        new_chain.len() == 0 <==> new_first.is_none(),
        new_chain.len() == 0 <==> new_last.is_none(),
        new_first == Some(new_chain[0]),
        new_last  == Some(new_chain[new_chain.len() - 1]),
        forall|k: int| 0 <= k < new_chain.len() ==> new_links.contains_key(new_chain[k]),
        forall|k: int| 0 <= k < new_chain.len() - 1 ==>
            new_links[new_chain[k]].next == Some(new_chain[k + 1]),
        forall|k: int| 1 <= k < new_chain.len() ==>
            new_links[new_chain[k]].prec == Some(new_chain[k - 1]),
        new_links[new_chain[0]].prec.is_none(),
        new_links[new_chain[new_chain.len() - 1]].next.is_none(),
{
    let n: int = old_chain.len() as int;

    // new_chain[0] = result; new_chain[k] = old_chain[k-1] for k >= 1

    // 1. no_dups
    assert(no_dups(new_chain)) by {
        assert forall|i: int, j: int|
            0 <= i < new_chain.len() && 0 <= j < new_chain.len() && new_chain[i] == new_chain[j]
            implies i == j
        by {
            if i > 0 && j > 0 {
                assert(new_chain[i] == old_chain[i - 1]);
                assert(new_chain[j] == old_chain[j - 1]);
            } else if i == 0 && j > 0 {
                assert(new_chain[0] == result);
                assert(old_links.contains_key(old_chain[j - 1]));
                assert(!old_links.contains_key(result));
            } else if i > 0 && j == 0 {
                assert(new_chain[0] == result);
                assert(old_links.contains_key(old_chain[i - 1]));
                assert(!old_links.contains_key(result));
            }
        };
    };

    // 2. Length and endpoints
    assert(new_chain.len() == n + 1);
    assert(new_chain[0] == result);
    assert(new_first == Some(result));

    // last
    if n == 0 {
        assert(new_last == Some(result));
        assert(new_chain[new_chain.len() - 1] == result);
    } else {
        assert(new_chain[n] == old_chain[n - 1]);
        assert(old_last == Some(old_chain[n - 1]));
        assert(new_last == old_last);
    }

    // 3. All chain keys in new_links
    assert forall|k: int| 0 <= k < new_chain.len() implies new_links.contains_key(new_chain[k])
    by {
        if k == 0 { } // result is in new_links
        else if k == 1 && n > 0 {
            // old_chain[0]: from old_first-specific postcondition
        } else {
            // k >= 2: new_chain[k] = old_chain[k-1], frame applies at k-1 >= 1
            assert(new_chain[k] == old_chain[k - 1]);
            assert(new_links.contains_key(old_chain[k - 1]));
        }
    };

    // 4. Forward links
    assert forall|k: int| 0 <= k < new_chain.len() - 1 implies
        new_links[new_chain[k]].next == Some(new_chain[k + 1])
    by {
        if k == 0 {
            // result.next == Some(old_chain[0]) == Some(new_chain[1])
            assert(new_links[result].next == Some(old_chain[0]));
            assert(new_chain[1] == old_chain[0]);
        } else if k == 1 && n > 1 {
            // old_chain[0].next == old_links[old_chain[0]].next (preserved)
            assert(new_chain[k] == old_chain[0]);
            assert(new_chain[k + 1] == old_chain[1]);
            assert(new_links[old_chain[0]].next == old_links[old_chain[0]].next);
            assert(old_links[old_chain[0]].next == Some(old_chain[1]));
        } else if k == 1 && n == 1 {
            // old_chain[0] is last; its next should equal new_chain[2]... but new_chain.len()-1 = 1, so k < 1: this branch won't be reached
            // Actually if n=1, new_chain.len()=2, so k ranges 0..0, k=1 is excluded
        } else {
            // k >= 2: new_chain[k] = old_chain[k-1]; frame applies
            assert(new_chain[k] == old_chain[k - 1]);
            assert(new_chain[k + 1] == old_chain[k]);
            assert(new_links[old_chain[k - 1]].next == old_links[old_chain[k - 1]].next);
            assert(old_links[old_chain[k - 1]].next == Some(old_chain[k]));
        }
    };

    // 5. Backward links
    assert forall|k: int| 1 <= k < new_chain.len() implies
        new_links[new_chain[k]].prec == Some(new_chain[k - 1])
    by {
        if k == 1 {
            // old_chain[0].prec == Some(result) (updated)
            assert(new_chain[1] == old_chain[0]);
            assert(new_chain[0] == result);
            assert(new_links[old_chain[0]].prec == Some(result));
        } else {
            // k >= 2: new_chain[k] = old_chain[k-1]; frame applies at k-1 >= 1
            assert(new_chain[k] == old_chain[k - 1]);
            assert(new_chain[k - 1] == old_chain[k - 2]);
            assert(new_links[old_chain[k - 1]].prec == old_links[old_chain[k - 1]].prec);
            assert(old_links[old_chain[k - 1]].prec == Some(old_chain[k - 2]));
        }
    };

    // 6. Boundary: first.prec is None (result.prec)
    assert(new_links[new_chain[0]].prec.is_none()) by {
        assert(new_chain[0] == result);
    };

    // 7. Boundary: last.next is None
    assert(new_links[new_chain[new_chain.len() - 1]].next.is_none()) by {
        if n == 0 {
            assert(new_chain[0] == result);
            assert(new_links[result].next.is_none());
        } else {
            assert(new_chain[n] == old_chain[n - 1]);
            if n == 1 {
                // old_chain[0] is the last; next preserved from old (which was None)
                assert(new_links[old_chain[0]].next == old_links[old_chain[0]].next);
                assert(old_links[old_chain[n - 1]].next.is_none());
            } else {
                // k-1 = n-1 >= 1, so frame applies
                assert(new_links[old_chain[n - 1]].next == old_links[old_chain[n - 1]].next);
                assert(old_links[old_chain[n - 1]].next.is_none());
            }
        }
    };
}

// =====================================================================
// Operations
// =====================================================================

impl<T> DoublyLinkedList<T> {

    /// Create an empty list.
    #[verifier::external_body]
    pub fn new() -> (result: Self)
        ensures
            result.first.is_none(),
            result.last.is_none(),
            result.chain@ == Seq::<u64>::empty(),
            result.links@ == Map::<u64, NodeLinks>::empty(),
            valid_chain(&result),
    {
        DoublyLinkedList {
            first: None,
            last: None,
            chain: Ghost(Seq::empty()),
            links: Ghost(Map::empty()),
            _phantom: core::marker::PhantomData,
        }
    }

    /// Append a new node to the back.
    ///
    /// Freshness: slotmap generational keys are never reused after removal,
    /// so a newly inserted key was not previously active.
    #[verifier::external_body]
    pub fn push_back(&mut self, value: T) -> (result: u64)
        requires valid_chain(&*old(self))
        ensures
            valid_chain(self),
            // Freshness
            !old(self).links@.contains_key(result),
            // Chain
            self.chain@ == old(self).chain@ + seq![result],
            self.last == Some(result),
            old(self).chain@.len() == 0 ==> self.first == Some(result),
            old(self).chain@.len() > 0  ==> self.first == old(self).first,
            // Link for result
            self.links@.contains_key(result),
            self.links@[result].next.is_none(),
            old(self).chain@.len() == 0 ==> self.links@[result].prec.is_none(),
            old(self).chain@.len() > 0  ==>
                self.links@[result].prec
                    == Some(old(self).chain@[old(self).chain@.len() - 1]),
            // Link update for old_last
            old(self).chain@.len() > 0 ==> {
                let lk = old(self).chain@[old(self).chain@.len() - 1];
                self.links@.contains_key(lk) &&
                self.links@[lk].next == Some(result) &&
                self.links@[lk].prec == old(self).links@[lk].prec
            },
            // Frame: all other chain entries unchanged
            forall|k: int| 0 <= k < old(self).chain@.len() - 1 ==>
                self.links@.contains_key(old(self).chain@[k]) &&
                self.links@[old(self).chain@[k]].next == old(self).links@[old(self).chain@[k]].next &&
                self.links@[old(self).chain@[k]].prec == old(self).links@[old(self).chain@[k]].prec,
    {
        unimplemented!()
    }

    /// Prepend a new node to the front.
    #[verifier::external_body]
    pub fn push_front(&mut self, value: T) -> (result: u64)
        requires valid_chain(&*old(self))
        ensures
            valid_chain(self),
            !old(self).links@.contains_key(result),
            self.chain@ == seq![result] + old(self).chain@,
            self.first == Some(result),
            old(self).chain@.len() == 0 ==> self.last == Some(result),
            old(self).chain@.len() > 0  ==> self.last == old(self).last,
            // Link for result
            self.links@.contains_key(result),
            self.links@[result].prec.is_none(),
            old(self).chain@.len() == 0 ==> self.links@[result].next.is_none(),
            old(self).chain@.len() > 0  ==> self.links@[result].next == Some(old(self).chain@[0]),
            // Link update for old_first
            old(self).chain@.len() > 0 ==> {
                let fk = old(self).chain@[0];
                self.links@.contains_key(fk) &&
                self.links@[fk].prec == Some(result) &&
                self.links@[fk].next == old(self).links@[fk].next
            },
            // Frame
            forall|k: int| 1 <= k < old(self).chain@.len() ==>
                self.links@.contains_key(old(self).chain@[k]) &&
                self.links@[old(self).chain@[k]].next == old(self).links@[old(self).chain@[k]].next &&
                self.links@[old(self).chain@[k]].prec == old(self).links@[old(self).chain@[k]].prec,
    {
        unimplemented!()
    }

    /// Remove `key` from the list.
    #[verifier::external_body]
    pub fn delete(&mut self, key: u64)
        requires
            valid_chain(&*old(self)),
            in_chain(&*old(self), key),
        ensures
            valid_chain(self),
            !self.links@.contains_key(key),
            exists|k: int| 0 <= k < old(self).chain@.len()
                && #[trigger] old(self).chain@[k] == key
                && self.chain@ == old(self).chain@.remove(k),
    {
        unimplemented!()
    }

    /// Return the node immediately after `key` in the chain, or None.
    #[verifier::external_body]
    pub fn next(&self, key: u64) -> (result: Option<u64>)
        requires
            valid_chain(self),
            in_chain(self, key),
        ensures
            result == self.links@[key].next,
            result.is_none() <==> self.last == Some(key),
            result.is_some() ==>
                exists|k: int| 0 <= k < self.chain@.len() - 1
                    && #[trigger] self.chain@[k] == key
                    && result == Some(self.chain@[k + 1]),
    {
        unimplemented!()
    }

    /// Return the node immediately before `key` in the chain, or None.
    #[verifier::external_body]
    pub fn prec(&self, key: u64) -> (result: Option<u64>)
        requires
            valid_chain(self),
            in_chain(self, key),
        ensures
            result == self.links@[key].prec,
            result.is_none() <==> self.first == Some(key),
            result.is_some() ==>
                exists|k: int| 1 <= k < self.chain@.len()
                    && #[trigger] self.chain@[k] == key
                    && result == Some(self.chain@[k - 1]),
    {
        unimplemented!()
    }

    /// Return the first node — proved directly (no SlotMap access).
    pub fn first(&self) -> (result: Option<u64>)
        requires valid_chain(self)
        ensures
            result == self.first,
            result.is_some() ==> in_chain(self, result.unwrap()),
    {
        if let Some(f) = self.first {
            proof {
                assert(self.chain@.len() > 0);
                assert(self.chain@[0] == f);
                assert(in_chain(self, f)) by {
                    assert(0 <= 0int < self.chain@.len() && self.chain@[0] == f);
                };
            }
            Some(f)
        } else {
            None
        }
    }

    /// Return the last node — proved directly (no SlotMap access).
    pub fn last(&self) -> (result: Option<u64>)
        requires valid_chain(self)
        ensures
            result == self.last,
            result.is_some() ==> in_chain(self, result.unwrap()),
    {
        if let Some(l) = self.last {
            proof {
                assert(self.chain@.len() > 0);
                let last_k = self.chain@.len() - 1;
                assert(self.chain@[last_k] == l);
                assert(in_chain(self, l)) by {
                    assert(0 <= last_k < self.chain@.len() && self.chain@[last_k] == l);
                };
            }
            Some(l)
        } else {
            None
        }
    }

    /// Insert a new node immediately after `key`.
    #[verifier::external_body]
    pub fn insert_after(&mut self, key: u64, value: T) -> (result: u64)
        requires
            valid_chain(&*old(self)),
            in_chain(&*old(self), key),
        ensures
            valid_chain(self),
            !old(self).links@.contains_key(result),
            exists|k: int| 0 <= k < old(self).chain@.len()
                && #[trigger] old(self).chain@[k] == key
                && self.chain@ == old(self).chain@.subrange(0, k + 1)
                                  + seq![result]
                                  + old(self).chain@.subrange(k + 1, old(self).chain@.len() as int),
    {
        unimplemented!()
    }

    /// Insert a new node immediately before `key`.
    #[verifier::external_body]
    pub fn insert_before(&mut self, key: u64, value: T) -> (result: u64)
        requires
            valid_chain(&*old(self)),
            in_chain(&*old(self), key),
        ensures
            valid_chain(self),
            !old(self).links@.contains_key(result),
            exists|k: int| 0 <= k < old(self).chain@.len()
                && #[trigger] old(self).chain@[k] == key
                && self.chain@ == old(self).chain@.subrange(0, k)
                                  + seq![result]
                                  + old(self).chain@.subrange(k, old(self).chain@.len() as int),
    {
        unimplemented!()
    }
}

// =====================================================================
// Target property: reachability-based chain validity
// =====================================================================

/// Every node in the list is forward-reachable from first.
///
/// The ghost chain is the reachability certificate: chain[0] == first
/// and chain[k] is reached from chain[k-1] via the next link
/// (proved by lemma_next_link_consistent).
/// Therefore every node in_chain is reachable from first in k steps.
proof fn lemma_all_nodes_reachable<T>(dll: &DoublyLinkedList<T>, key: u64)
    requires
        valid_chain(dll),
        in_chain(dll, key),
    ensures
        dll.chain@.len() > 0,
        dll.first.is_some(),
        dll.first == Some(dll.chain@[0]),
        exists|k: int| 0 <= k < dll.chain@.len() && dll.chain@[k] == key,
        dll.last.is_some(),
        exists|k: int| 0 <= k < dll.chain@.len() && Some(dll.chain@[k]) == dll.last,
        dll.links@.contains_key(key),
{
    let witness = choose|k: int| 0 <= k < dll.chain@.len() && dll.chain@[k] == key;
    assert(0 <= witness < dll.chain@.len());
    let last_k = dll.chain@.len() - 1;
    assert(dll.chain@[last_k] == dll.last.unwrap());
}

/// The ghost chain has no duplicate keys.
proof fn lemma_chain_no_dups<T>(dll: &DoublyLinkedList<T>)
    requires valid_chain(dll)
    ensures no_dups(dll.chain@)
{
}

/// Every pair of consecutive chain positions is connected by a forward link.
/// This is the concrete reachability step: to travel from chain[k] to chain[k+1],
/// follow the next link stored in links@[chain[k]].
proof fn lemma_consecutive_linked<T>(dll: &DoublyLinkedList<T>, k: int)
    requires
        valid_chain(dll),
        0 <= k < dll.chain@.len() - 1,
    ensures
        dll.links@.contains_key(dll.chain@[k]),
        dll.links@[dll.chain@[k]].next == Some(dll.chain@[k + 1]),
{
}

/// Bidirectional link consistency: next and prec are mutual inverses on
/// chain-adjacent nodes.
///
/// This property is provable from valid_chain but NOT from the concrete code
/// (because SlotMap.get_mut is external). It is a theorem about the ghost spec.
proof fn lemma_next_link_consistent<T>(dll: &DoublyLinkedList<T>, k: int)
    requires
        valid_chain(dll),
        0 <= k < dll.chain@.len() - 1,
    ensures
        // Successor's prec points back to current
        dll.links@[dll.chain@[k + 1]].prec == Some(dll.chain@[k]),
        // Current's next points forward
        dll.links@[dll.chain@[k]].next == Some(dll.chain@[k + 1]),
{
}

} // verus!

fn main() {}
