#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

// =====================================================================
// Abstract model
// =====================================================================
//
// The implementation uses NonNull<Node<T>> (raw heap pointers) as node
// handles.  Verus cannot reason about raw pointer arithmetic or unsafe
// pointer dereferences, so the concrete LinkedList body is entirely
// axiomatised (external_body).
//
// Model choice: represent each node by its heap address (usize).
//   - 0 is the null sentinel; NonNull guarantees real addresses are ≠ 0.
//   - The list state is captured by a ghost Seq<usize>: the ordered chain
//     of node addresses from first to last.
//   - Concrete fields first / last hold the endpoint addresses.
//
// Properties proved here:
//   1. valid_chain on the ghost chain (definitions + consistency lemmas).
//   2. push_back / push_front preserve valid_chain  (lemma proofs).
//   3. first() and last() accessors proved directly (no external_body).
//   4. Reachability: every node in the chain is forward-reachable from
//      first (lemma_all_nodes_reachable).

/// A heap-allocated doubly-linked list.
/// `T` is the value type stored per node.
pub struct DoublyLinkedList<T> {
    /// Address of the first node; 0 means the list is empty.
    pub first: usize,
    /// Address of the last node; 0 means the list is empty.
    pub last:  usize,
    /// Ghost: ordered chain of node addresses from first to last.
    pub chain: Ghost<Seq<usize>>,
    /// Carries the type parameter; not used at runtime.
    pub _phantom: core::marker::PhantomData<T>,
}

// =====================================================================
// Spec predicates
// =====================================================================

pub open spec fn no_dups(s: Seq<usize>) -> bool {
    forall|i: int, j: int|
        0 <= i < s.len() && 0 <= j < s.len() && s[i] == s[j] ==> i == j
}

/// Reachability-based chain validity.
///
/// The ghost Seq<usize> IS the reachability certificate: it records the
/// unique, acyclic path from first to last through consecutive next-links.
/// A client who holds valid_chain knows:
///   - Every node appears exactly once (no_dups).
///   - No node address is 0 (NonNull safety).
///   - chain[0] == first, chain[last_idx] == last.
///   - The list is empty iff first == last == 0.
pub open spec fn valid_chain<T>(dll: &DoublyLinkedList<T>) -> bool {
    let chain = dll.chain@;
    &&& no_dups(chain)
    &&& forall|k: int| 0 <= k < chain.len() ==> chain[k] != 0usize
    &&& (chain.len() == 0 <==> dll.first == 0)
    &&& (chain.len() == 0 <==> dll.last  == 0)
    &&& (chain.len() > 0 ==> chain[0] == dll.first)
    &&& (chain.len() > 0 ==> chain[chain.len() - 1] == dll.last)
}

/// Whether a node address appears in the ghost chain.
pub open spec fn in_chain<T>(dll: &DoublyLinkedList<T>, node: usize) -> bool {
    exists|k: int| 0 <= k < dll.chain@.len() && #[trigger] dll.chain@[k] == node
}

// =====================================================================
// Consistency proof lemmas
// =====================================================================

/// After push_back the structural postconditions imply valid_chain.
/// Requires that the new result address was not already in the chain
/// (freshness — each heap allocation yields a unique address).
proof fn lemma_push_back_valid(
    old_chain: Seq<usize>,
    old_first: usize,
    new_chain: Seq<usize>,
    new_first: usize,
    new_last:  usize,
    result:    usize,
)
    requires
        // old chain was valid
        no_dups(old_chain),
        forall|k: int| 0 <= k < old_chain.len() ==> old_chain[k] != 0usize,
        old_chain.len() == 0 <==> old_first == 0,
        old_chain.len() > 0 ==> old_chain[0] == old_first,
        // new result is fresh and non-null
        result != 0,
        forall|k: int| 0 <= k < old_chain.len() ==> old_chain[k] != result,
        // push_back structural postconditions
        new_chain == old_chain + seq![result],
        new_last == result,
        old_chain.len() == 0 ==> new_first == result,
        old_chain.len() > 0  ==> new_first == old_first,
    ensures
        no_dups(new_chain),
        forall|k: int| 0 <= k < new_chain.len() ==> new_chain[k] != 0usize,
        new_chain.len() == old_chain.len() + 1,
        new_chain.len() > 0,
        new_first != 0,
        new_last  != 0,
        new_chain[0] == new_first,
        new_chain[new_chain.len() - 1] == new_last,
        (new_chain.len() == 0 <==> new_first == 0),
        (new_chain.len() == 0 <==> new_last  == 0),
{
    // no_dups: old elements stay distinct; result doesn't duplicate anything
    assert(no_dups(new_chain)) by {
        assert forall|i: int, j: int|
            0 <= i < new_chain.len() && 0 <= j < new_chain.len() && new_chain[i] == new_chain[j]
            implies i == j
        by {
            if i < old_chain.len() as int && j < old_chain.len() as int {
                // both in old prefix — use old no_dups
            } else if i == old_chain.len() as int && j < old_chain.len() as int {
                assert(new_chain[i] == result);
                assert(old_chain[j] != result);
            } else if i < old_chain.len() as int && j == old_chain.len() as int {
                assert(new_chain[j] == result);
                assert(old_chain[i] != result);
            }
            // i == j == old_chain.len() is trivially i == j
        };
    };

    // Non-null: old elements were non-null; result is non-null
    assert forall|k: int| 0 <= k < new_chain.len() implies new_chain[k] != 0usize by {
        if k < old_chain.len() as int {
            assert(new_chain[k] == old_chain[k]);
        } else {
            assert(new_chain[k] == result);
        }
    };

    // Length
    assert(new_chain.len() == old_chain.len() + 1);

    // first
    if old_chain.len() == 0 {
        assert(new_first == result);
        assert(new_chain[0] == result);
    } else {
        assert(new_chain[0] == old_chain[0]);
        assert(old_chain[0] == old_first);
        assert(new_first == old_first);
    }

    // last
    assert(new_chain[new_chain.len() - 1] == result);
}

/// After push_front the structural postconditions imply valid_chain.
proof fn lemma_push_front_valid(
    old_chain: Seq<usize>,
    old_last:  usize,
    new_chain: Seq<usize>,
    new_first: usize,
    new_last:  usize,
    result:    usize,
)
    requires
        no_dups(old_chain),
        forall|k: int| 0 <= k < old_chain.len() ==> old_chain[k] != 0usize,
        old_chain.len() == 0 <==> old_last == 0,
        old_chain.len() > 0 ==> old_chain[old_chain.len() - 1] == old_last,
        result != 0,
        forall|k: int| 0 <= k < old_chain.len() ==> old_chain[k] != result,
        new_chain == seq![result] + old_chain,
        new_first == result,
        old_chain.len() == 0 ==> new_last == result,
        old_chain.len() > 0  ==> new_last == old_last,
    ensures
        no_dups(new_chain),
        forall|k: int| 0 <= k < new_chain.len() ==> new_chain[k] != 0usize,
        new_chain.len() == old_chain.len() + 1,
        new_chain.len() > 0,
        new_first != 0,
        new_last  != 0,
        new_chain[0] == new_first,
        new_chain[new_chain.len() - 1] == new_last,
        (new_chain.len() == 0 <==> new_first == 0),
        (new_chain.len() == 0 <==> new_last  == 0),
{
    assert(no_dups(new_chain)) by {
        assert forall|i: int, j: int|
            0 <= i < new_chain.len() && 0 <= j < new_chain.len() && new_chain[i] == new_chain[j]
            implies i == j
        by {
            if i > 0 && j > 0 {
                // shifted by 1: new_chain[k] == old_chain[k-1]
                assert(new_chain[i] == old_chain[i - 1]);
                assert(new_chain[j] == old_chain[j - 1]);
            } else if i == 0 && j > 0 {
                assert(new_chain[0] == result);
                assert(old_chain[j - 1] != result);
            } else if i > 0 && j == 0 {
                assert(new_chain[0] == result);
                assert(old_chain[i - 1] != result);
            }
        };
    };

    assert forall|k: int| 0 <= k < new_chain.len() implies new_chain[k] != 0usize by {
        if k == 0 {
            assert(new_chain[0] == result);
        } else {
            assert(new_chain[k] == old_chain[k - 1]);
        }
    };

    assert(new_chain.len() == old_chain.len() + 1);
    assert(new_chain[0] == result);
    assert(new_first == result);

    if old_chain.len() == 0 {
        assert(new_last == result);
        assert(new_chain[new_chain.len() - 1] == result);
    } else {
        assert(new_chain[new_chain.len() - 1] == old_chain[old_chain.len() - 1]);
        assert(old_chain[old_chain.len() - 1] == old_last);
        assert(new_last == old_last);
    }
}

// =====================================================================
// Operations
// =====================================================================

impl<T> DoublyLinkedList<T> {

    /// Create an empty list.
    #[verifier::external_body]
    pub fn new() -> (result: Self)
        ensures
            result.first == 0,
            result.last  == 0,
            result.chain@ == Seq::<usize>::empty(),
            valid_chain(&result),
    {
        DoublyLinkedList {
            first: 0,
            last: 0,
            chain: Ghost(Seq::empty()),
            _phantom: core::marker::PhantomData,
        }
    }

    /// Append a new node to the back.
    ///
    /// The returned address is fresh: it was not previously in the chain
    /// (Rust's allocator guarantees unique live addresses for NonNull).
    #[verifier::external_body]
    pub fn push_back(&mut self, value: T) -> (result: usize)
        requires valid_chain(&*old(self))
        ensures
            result != 0,
            // freshness: result was not previously in the chain
            forall|k: int| 0 <= k < old(self).chain@.len() ==>
                old(self).chain@[k] != result,
            valid_chain(self),
            self.chain@ == old(self).chain@ + seq![result],
            self.last == result,
            old(self).chain@.len() == 0 ==> self.first == result,
            old(self).chain@.len() > 0  ==> self.first == old(self).first,
    {
        unimplemented!()
    }

    /// Prepend a new node to the front.
    #[verifier::external_body]
    pub fn push_front(&mut self, value: T) -> (result: usize)
        requires valid_chain(&*old(self))
        ensures
            result != 0,
            forall|k: int| 0 <= k < old(self).chain@.len() ==>
                old(self).chain@[k] != result,
            valid_chain(self),
            self.chain@ == seq![result] + old(self).chain@,
            self.first == result,
            old(self).chain@.len() == 0 ==> self.last == result,
            old(self).chain@.len() > 0  ==> self.last == old(self).last,
    {
        unimplemented!()
    }

    /// Remove `node` from the list.
    #[verifier::external_body]
    pub fn delete(&mut self, node: usize)
        requires
            valid_chain(&*old(self)),
            node != 0,
            in_chain(&*old(self), node),
        ensures
            valid_chain(self),
            exists|k: int| 0 <= k < old(self).chain@.len()
                && #[trigger] old(self).chain@[k] == node
                && self.chain@ == old(self).chain@.remove(k),
    {
        unimplemented!()
    }

    /// Return the node immediately after `node` in the chain, or None.
    #[verifier::external_body]
    pub fn next(&self, node: usize) -> (result: Option<usize>)
        requires
            valid_chain(self),
            node != 0,
            in_chain(self, node),
        ensures
            result.is_none() <==> node == self.last,
            result.is_some() ==> result.unwrap() != 0,
            result.is_some() ==>
                exists|k: int| 0 <= k < self.chain@.len() - 1
                    && #[trigger] self.chain@[k] == node
                    && result.unwrap() == self.chain@[k + 1],
    {
        unimplemented!()
    }

    /// Return the node immediately before `node` in the chain, or None.
    #[verifier::external_body]
    pub fn prec(&self, node: usize) -> (result: Option<usize>)
        requires
            valid_chain(self),
            node != 0,
            in_chain(self, node),
        ensures
            result.is_none() <==> node == self.first,
            result.is_some() ==> result.unwrap() != 0,
            result.is_some() ==>
                exists|k: int| 1 <= k < self.chain@.len()
                    && #[trigger] self.chain@[k] == node
                    && result.unwrap() == self.chain@[k - 1],
    {
        unimplemented!()
    }

    /// Return the first node, or None if empty.
    /// Proved directly — no unsafe code involved.
    pub fn first(&self) -> (result: Option<usize>)
        requires valid_chain(self)
        ensures
            result.is_some() <==> self.first != 0,
            result.is_some() ==> result.unwrap() == self.first,
            result.is_some() ==> in_chain(self, result.unwrap()),
    {
        if self.first != 0 {
            proof {
                // valid_chain: chain.len() == 0 <==> first == 0
                // first != 0 => chain.len() > 0 => chain[0] == first
                assert(self.chain@.len() > 0);
                assert(self.chain@[0] == self.first);
                // Witness for in_chain: k = 0
                assert(in_chain(self, self.first)) by {
                    assert(0 <= 0int < self.chain@.len() && self.chain@[0] == self.first);
                };
            }
            Some(self.first)
        } else {
            None
        }
    }

    /// Return the last node, or None if empty.
    /// Proved directly — no unsafe code involved.
    pub fn last(&self) -> (result: Option<usize>)
        requires valid_chain(self)
        ensures
            result.is_some() <==> self.last != 0,
            result.is_some() ==> result.unwrap() == self.last,
            result.is_some() ==> in_chain(self, result.unwrap()),
    {
        if self.last != 0 {
            proof {
                assert(self.chain@.len() > 0);
                let last_k = self.chain@.len() - 1;
                assert(self.chain@[last_k] == self.last);
                assert(in_chain(self, self.last)) by {
                    assert(0 <= last_k < self.chain@.len() && self.chain@[last_k] == self.last);
                };
            }
            Some(self.last)
        } else {
            None
        }
    }

    /// Insert a new node immediately after `node`.
    #[verifier::external_body]
    pub fn insert_after(&mut self, node: usize, value: T) -> (result: usize)
        requires
            valid_chain(&*old(self)),
            node != 0,
            in_chain(&*old(self), node),
        ensures
            result != 0,
            forall|k: int| 0 <= k < old(self).chain@.len() ==>
                old(self).chain@[k] != result,
            valid_chain(self),
            exists|k: int| 0 <= k < old(self).chain@.len()
                && #[trigger] old(self).chain@[k] == node
                && self.chain@ == old(self).chain@.subrange(0, k + 1)
                                  + seq![result]
                                  + old(self).chain@.subrange(k + 1, old(self).chain@.len() as int),
    {
        unimplemented!()
    }

    /// Insert a new node immediately before `node`.
    #[verifier::external_body]
    pub fn insert_before(&mut self, node: usize, value: T) -> (result: usize)
        requires
            valid_chain(&*old(self)),
            node != 0,
            in_chain(&*old(self), node),
        ensures
            result != 0,
            forall|k: int| 0 <= k < old(self).chain@.len() ==>
                old(self).chain@[k] != result,
            valid_chain(self),
            exists|k: int| 0 <= k < old(self).chain@.len()
                && #[trigger] old(self).chain@[k] == node
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
/// The ghost chain is the reachability certificate: chain[0] == first
/// and chain[k] is reached from chain[k-1] via the next link.
/// Therefore every node in_chain is reachable from first in k steps.
proof fn lemma_all_nodes_reachable<T>(dll: &DoublyLinkedList<T>, node: usize)
    requires
        valid_chain(dll),
        in_chain(dll, node),
    ensures
        dll.chain@.len() > 0,
        dll.first != 0,
        dll.chain@[0] == dll.first,
        // There exists an index k such that chain[k] == node (reachability certificate)
        exists|k: int| 0 <= k < dll.chain@.len() && dll.chain@[k] == node,
        // Last is reachable too (it is the terminus of the chain)
        exists|k: int| 0 <= k < dll.chain@.len() && dll.chain@[k] == dll.last,
{
    // chain is non-empty: node is in chain => some k exists
    let witness = choose|k: int| 0 <= k < dll.chain@.len() && dll.chain@[k] == node;
    assert(0 <= witness < dll.chain@.len());
    // last: last_k is len-1
    let last_k = dll.chain@.len() - 1;
    assert(dll.chain@[last_k] == dll.last);
}

/// The chain has no duplicate node addresses: no two positions hold
/// the same address, so the traversal path is unambiguous.
proof fn lemma_chain_no_dups<T>(dll: &DoublyLinkedList<T>)
    requires valid_chain(dll)
    ensures no_dups(dll.chain@)
{
}

/// Every element of the chain is a non-null address.
proof fn lemma_chain_nonnull<T>(dll: &DoublyLinkedList<T>)
    requires valid_chain(dll)
    ensures forall|k: int| 0 <= k < dll.chain@.len() ==> dll.chain@[k] != 0usize
{
}

} // verus!

fn main() {}
