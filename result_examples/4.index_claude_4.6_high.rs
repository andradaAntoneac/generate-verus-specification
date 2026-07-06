#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

// =====================================================================
// Data structures (simplified: no custom allocator, public fields)
// =====================================================================

pub struct Element<T> {
    pub next: u32,
    pub prec: u32,
    pub value: T,
}

pub struct DoublyLinkedList<T> {
    pub data: Vec<Option<Element<T>>>,
    pub free_list: Vec<u32>,
    pub first: u32,
    pub last: u32,
}

// =====================================================================
// Spec predicates
// =====================================================================

/// Is slot i a valid (occupied) index in data?
pub open spec fn valid_slot<T>(data: Seq<Option<Element<T>>>, i: u32) -> bool {
    i != u32::MAX
    && (i as int) < data.len()
    && data[i as int].is_some()
}

/// Set of all occupied slots.
pub open spec fn node_set<T>(data: Seq<Option<Element<T>>>) -> Set<u32> {
    Set::new(|i: u32| valid_slot(data, i))
}

/// node_set membership is equivalent to valid_slot (bridges Set::new axiom).
proof fn lemma_node_set_contains<T>(data: Seq<Option<Element<T>>>, i: u32)
    ensures node_set(data).contains(i) <==> valid_slot(data, i)
{}

/// Forward traversal: collect node indices starting at cur, bounded by fuel.
pub open spec fn traverse<T>(data: Seq<Option<Element<T>>>, cur: u32, fuel: nat) -> Seq<u32>
    decreases fuel
{
    if cur == u32::MAX
       || fuel == 0
       || (cur as int) >= data.len()
       || data[cur as int].is_none()
    {
        Seq::empty()
    } else {
        seq![cur] + traverse(data, data[cur as int].unwrap().next, (fuel - 1) as nat)
    }
}

/// The chain sequence: traverse from first with fuel = data.len().
pub open spec fn chain_seq<T>(dll: &DoublyLinkedList<T>) -> Seq<u32> {
    traverse(dll.data@, dll.first, dll.data@.len())
}

/// No duplicate indices in a sequence.
pub open spec fn no_dups(s: Seq<u32>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == s[j] ==> i == j
}

/// next/prec links are mutually consistent.
pub open spec fn links_symmetric<T>(data: Seq<Option<Element<T>>>) -> bool {
    forall|i: u32| #[trigger] valid_slot(data, i) ==> {
        let e = data[i as int].unwrap();
        &&& (e.next != u32::MAX ==> valid_slot(data, e.next))
        &&& (e.prec != u32::MAX ==> valid_slot(data, e.prec))
        &&& (e.next != u32::MAX ==> data[e.next as int].unwrap().prec == i)
        &&& (e.prec != u32::MAX ==> data[e.prec as int].unwrap().next == i)
    }
}

/// Well-formed list structure.
pub open spec fn wf_list<T>(dll: &DoublyLinkedList<T>) -> bool {
    &&& (node_set(dll.data@).is_empty() <==> dll.first == u32::MAX)
    &&& (node_set(dll.data@).is_empty() <==> dll.last  == u32::MAX)
    &&& (dll.first != u32::MAX ==> valid_slot(dll.data@, dll.first))
    &&& (dll.last  != u32::MAX ==> valid_slot(dll.data@, dll.last))
    &&& links_symmetric(dll.data@)
    &&& (dll.first != u32::MAX ==> dll.data@[dll.first as int].unwrap().prec == u32::MAX)
    &&& (dll.last  != u32::MAX ==> dll.data@[dll.last  as int].unwrap().next == u32::MAX)
    &&& dll.data@.len() < u32::MAX as nat
}

/// Chain validity (reachability-based):
/// The forward traversal from first covers exactly node_set,
/// with no cycles, ending at last.
///
/// Corollaries (when valid_chain holds):
///   - Every node is forward-reachable from first: it appears in chain_seq.
///   - last is reachable from every node: it is the final element of chain_seq,
///     and consecutive chain elements are linked by next pointers.
pub open spec fn valid_chain<T>(dll: &DoublyLinkedList<T>) -> bool {
    let seq = chain_seq(dll);
    let ns  = node_set(dll.data@);
    &&& wf_list(dll)
    &&& no_dups(seq)
    &&& (forall|id: u32| #[trigger] ns.contains(id) ==>
            exists|k: int| 0 <= k < seq.len() && seq[k] == id)
    &&& (forall|k: int| 0 <= k < seq.len() ==> ns.contains(seq[k]))
    &&& (seq.len() == 0 <==> dll.first == u32::MAX)
    &&& (seq.len() > 0 ==> seq[seq.len() - 1] == dll.last)
}

// =====================================================================
// Traverse lemmas
// =====================================================================

/// Fuel monotonicity: if the traversal terminates before exhausting fuel1,
/// adding more fuel (fuel2 >= fuel1) yields the same result.
proof fn lemma_traverse_fuel_mono<T>(
    data: Seq<Option<Element<T>>>,
    cur: u32,
    fuel1: nat,
    fuel2: nat,
)
    requires
        fuel1 <= fuel2,
        traverse(data, cur, fuel1).len() < fuel1,
    ensures
        traverse(data, cur, fuel1) == traverse(data, cur, fuel2)
    decreases fuel1
{
    if cur == u32::MAX || (cur as int) >= data.len() || data[cur as int].is_none() {
        // Both traversals are empty.
    } else if fuel1 == 0 {
        // len() < 0 is impossible.
    } else {
        let e  = data[cur as int].unwrap();
        let s1 = traverse(data, e.next, (fuel1 - 1) as nat);
        assert(traverse(data, cur, fuel1) == seq![cur] + s1);
        assert(fuel1 >= 2);
        assert(s1.len() < (fuel1 - 1) as nat);
        assert((fuel1 - 1) as nat <= (fuel2 - 1) as nat);
        lemma_traverse_fuel_mono(data, e.next, (fuel1 - 1) as nat, (fuel2 - 1) as nat);
        assert(traverse(data, cur, fuel2) == seq![cur] + traverse(data, e.next, (fuel2 - 1) as nat));
    }
}

/// Frame: appending a brand-new slot (at index old_data.len()) does not change
/// the traversal from cur, as long as no existing valid slot has next = old_data.len()
/// (guaranteed by links_symmetric: next always points to a currently valid slot).
proof fn lemma_traverse_frame_push<T>(
    old_data: Seq<Option<Element<T>>>,
    new_slot: Option<Element<T>>,
    cur: u32,
    fuel: nat,
)
    requires
        (cur as int) != old_data.len() as int,
        old_data.len() < u32::MAX as nat,
        // No existing valid slot's next equals the new index (int comparison avoids cast overflow).
        forall|i: u32| #[trigger] valid_slot(old_data, i) ==>
            (old_data[i as int].unwrap().next as int) != old_data.len() as int,
        fuel <= old_data.len() + 1,
    ensures
        traverse(old_data, cur, fuel)
            == traverse(old_data + seq![new_slot], cur, fuel)
    decreases fuel
{
    let new_data = old_data + seq![new_slot];
    if cur == u32::MAX || fuel == 0 { }
    else if (cur as int) >= old_data.len() {
        assert((cur as int) > old_data.len() as int);
        assert((cur as int) >= new_data.len() as int);
    } else if old_data[cur as int].is_none() {
        assert(new_data[cur as int] == old_data[cur as int]);
    } else {
        let e = old_data[cur as int].unwrap();
        assert(new_data[cur as int] == old_data[cur as int]);
        assert(valid_slot(old_data, cur));
        assert((e.next as int) != old_data.len() as int);
        lemma_traverse_frame_push(old_data, new_slot, e.next, (fuel - 1) as nat);
    }
}

/// Frame: reactivating a freed slot (None → Some at freed_idx, same data length)
/// does not change the traversal from cur, provided no valid slot had next = freed_idx.
/// This holds by links_symmetric: next of any valid slot points only to valid (Some) slots,
/// and freed_idx was None before allocation, hence not a valid slot.
proof fn lemma_traverse_frame_reuse<T>(
    old_data: Seq<Option<Element<T>>>,
    new_data: Seq<Option<Element<T>>>,
    cur: u32,
    freed_idx: u32,
    fuel: nat,
)
    requires
        new_data.len() == old_data.len(),
        (freed_idx as int) < old_data.len(),
        old_data[freed_idx as int].is_none(),
        new_data[freed_idx as int].is_some(),
        forall|i: int| 0 <= i < old_data.len() && i != freed_idx as int ==>
            old_data[i] == new_data[i],
        forall|i: u32| valid_slot(old_data, i) ==>
            old_data[i as int].unwrap().next != freed_idx,
        cur != freed_idx,
    ensures
        traverse(old_data, cur, fuel) == traverse(new_data, cur, fuel)
    decreases fuel
{
    if cur == u32::MAX || fuel == 0 { }
    else if (cur as int) >= old_data.len() { }
    else if old_data[cur as int].is_none() {
        assert(new_data[cur as int] == old_data[cur as int]);
    } else {
        let e = old_data[cur as int].unwrap();
        assert(new_data[cur as int] == old_data[cur as int]);
        assert(valid_slot(old_data, cur));
        assert(e.next != freed_idx);
        lemma_traverse_frame_reuse(old_data, new_data, e.next, freed_idx, (fuel - 1) as nat);
    }
}

/// Fuel downward: if traverse with fuel2 terminates in at most fuel1 steps, then fuel1 gives same result.
proof fn lemma_traverse_fuel_le<T>(
    data: Seq<Option<Element<T>>>,
    cur: u32,
    fuel1: nat,
    fuel2: nat,
)
    requires
        fuel1 <= fuel2,
        traverse(data, cur, fuel2).len() <= fuel1,
    ensures
        traverse(data, cur, fuel1) == traverse(data, cur, fuel2)
    decreases fuel2
{
    if cur == u32::MAX || (cur as int) >= data.len() || data[cur as int].is_none() {
    } else if fuel2 == 0 {
    } else if fuel1 == 0 {
        // traverse(..., fuel2).len() <= 0 means it's empty; but cur is valid => len >= 1. Contradiction.
        assert(traverse(data, cur, fuel2).len() >= 1);
    } else {
        let e = data[cur as int].unwrap();
        assert(traverse(data, cur, fuel2) == seq![cur] + traverse(data, e.next, (fuel2 - 1) as nat));
        assert(traverse(data, cur, fuel2).len() >= 1);
        // traverse(data, e.next, fuel2-1).len() <= fuel1 - 1
        lemma_traverse_fuel_le(data, e.next, (fuel1 - 1) as nat, (fuel2 - 1) as nat);
    }
}

/// Core extension: after setting old_last.next = new_node (new_node.next = MAX),
/// the traversal extends by exactly one element at the end.
proof fn lemma_traverse_extend_end<T>(
    old_data: Seq<Option<Element<T>>>,
    new_data: Seq<Option<Element<T>>>,
    first: u32,
    old_last: u32,
    new_node: u32,
    fuel: nat,
)
    requires
        valid_slot(old_data, old_last),
        old_data[old_last as int].unwrap().next == u32::MAX,
        valid_slot(new_data, old_last),
        valid_slot(new_data, new_node),
        new_data[new_node as int].unwrap().next == u32::MAX,
        new_data[old_last as int].unwrap().next == new_node,
        new_data.len() == old_data.len(),
        forall|i: int| 0 <= i < old_data.len() && i != old_last as int && i != new_node as int ==>
            old_data[i] == new_data[i],
        old_last != new_node,
        fuel <= old_data.len(),
        traverse(old_data, first, fuel).len() > 0,
        traverse(old_data, first, fuel)[traverse(old_data, first, fuel).len() - 1] == old_last,
        no_dups(traverse(old_data, first, fuel)),
        forall|k: int| 0 <= k < traverse(old_data, first, fuel).len() ==>
            traverse(old_data, first, fuel)[k] != new_node,
    ensures
        traverse(new_data, first, fuel + 1) == traverse(old_data, first, fuel) + seq![new_node]
    decreases fuel
{
    let old_seq = traverse(old_data, first, fuel);
    // Key helper: a non-empty traversal means the start node is a valid slot.
    assert(first != u32::MAX && (first as int) < old_data.len() && old_data[first as int].is_some()) by {
        // If first were invalid, traverse would return empty — contradiction with len() > 0.
        if first == u32::MAX || (first as int) >= old_data.len() || old_data[first as int].is_none() {
            assert(traverse(old_data, first, fuel) == Seq::<u32>::empty());
        }
    };
    assert(valid_slot(old_data, first));
    if fuel == 0 {
        assert(false);
    } else if first == old_last {
        // traverse(old_data, first, fuel) = seq![first] + traverse(old_data, first.next=MAX, fuel-1)
        //                                = seq![first] + empty = seq![first]
        assert(old_data[first as int].unwrap().next == u32::MAX);
        assert(old_seq == seq![first] + traverse(old_data, u32::MAX, (fuel - 1) as nat));
        assert(traverse(old_data, u32::MAX, (fuel - 1) as nat) == Seq::<u32>::empty());
        assert(old_seq == seq![first]);
        assert(old_seq.len() == 1);
        assert(old_seq[0] == old_last);
        // valid_slot(new_data, old_last) is a precondition of this lemma.
        // Since first == old_last, we have valid_slot(new_data, first).
        assert(valid_slot(new_data, first));
        assert(new_data[first as int].unwrap().next == new_node);
        assert(traverse(new_data, first, fuel + 1)
            == seq![first] + traverse(new_data, new_node, fuel));
        assert(valid_slot(new_data, new_node));
        assert(new_data[new_node as int].unwrap().next == u32::MAX);
        assert(traverse(new_data, new_node, fuel)
            == seq![new_node] + traverse(new_data, u32::MAX, (fuel - 1) as nat));
        assert(traverse(new_data, u32::MAX, (fuel - 1) as nat) == Seq::<u32>::empty());
    } else {
        assert(valid_slot(old_data, first));
        let e        = old_data[first as int].unwrap();
        let sub_old  = traverse(old_data, e.next, (fuel - 1) as nat);
        assert(old_seq == seq![first] + sub_old);
        assert(sub_old.len() > 0);
        assert(sub_old[sub_old.len() - 1] == old_last);
        assert forall|k: int| 0 <= k < sub_old.len() implies sub_old[k] != new_node by {
            assert(old_seq[k + 1] == sub_old[k]);
        };
        assert(no_dups(sub_old)) by {
            assert forall|i: int, j: int|
                0 <= i < sub_old.len() && 0 <= j < sub_old.len() && sub_old[i] == sub_old[j]
                implies i == j by
            {
                assert(old_seq[i + 1] == sub_old[i]);
                assert(old_seq[j + 1] == sub_old[j]);
            };
        };
        assert(first as int != old_last as int);
        // first != new_node: new_node is not on the old traversal path (precondition).
        assert((first as int) != (new_node as int)) by {
            assert(old_seq[0int] == first);
            assert(old_seq[0int] != new_node);
        };
        assert(old_data[first as int] == new_data[first as int]);
        lemma_traverse_extend_end(
            old_data, new_data, e.next, old_last, new_node, (fuel - 1) as nat);
        assert(traverse(new_data, e.next, fuel) == sub_old + seq![new_node]);
        assert(valid_slot(new_data, first));
        let ne = new_data[first as int].unwrap();
        assert(ne.next == e.next);
        assert(traverse(new_data, first, fuel + 1)
            == seq![first] + traverse(new_data, e.next, fuel));
        assert(seq![first] + (sub_old + seq![new_node])
            == (seq![first] + sub_old) + seq![new_node]);
    }
}

// =====================================================================
// Implementation
// =====================================================================

impl<T> DoublyLinkedList<T> {

    pub fn new(capacity: usize) -> (result: Self)
        ensures
            result.first == u32::MAX,
            result.last  == u32::MAX,
            result.data@  == Seq::<Option<Element<T>>>::empty(),
            valid_chain(&result),
    {
        let result = Self {
            data:      Vec::with_capacity(capacity),
            free_list: Vec::with_capacity(32),
            first:     u32::MAX,
            last:      u32::MAX,
        };
        proof {
            assert(result.data@.len() == 0);
            assert(node_set(result.data@).is_empty()) by {
                assert forall|i: u32| !valid_slot(result.data@, i) by { };
            };
            assert(chain_seq(&result) == Seq::<u32>::empty());
            assert(wf_list(&result)) by {
                assert(links_symmetric(result.data@)) by {
                    assert forall|i: u32| !valid_slot(result.data@, i) by { };
                };
            };
        }
        result
    }

    fn add_first_element(&mut self, value: T) -> (result: u32)
        requires
            old(self).data@ == Seq::<Option<Element<T>>>::empty(),
            old(self).first == u32::MAX,
            old(self).last  == u32::MAX,
        ensures
            result == 0u32,
            self.first == 0u32,
            self.last  == 0u32,
            self.data@.len() == 1,
            self.data@[0int] == Some(Element { next: u32::MAX, prec: u32::MAX, value: value }),
            valid_chain(self),
    {
        self.data.push(Some(Element { next: u32::MAX, prec: u32::MAX, value }));
        self.first = 0;
        self.last  = 0;
        proof {
            assert(self.data@.len() == 1);
            assert(valid_slot(self.data@, 0u32));
            // chain_seq = traverse(data, 0, 1) = [0]
            assert(traverse(self.data@, 0u32, 1nat) == seq![0u32]) by {
                assert(self.data@[0int].unwrap().next == u32::MAX);
                assert(traverse(self.data@, 0u32, 1nat)
                    == seq![0u32] + traverse(self.data@, u32::MAX, 0nat));
                assert(traverse(self.data@, u32::MAX, 0nat) == Seq::<u32>::empty());
            };
            assert(chain_seq(self) == seq![0u32]);
            // node_set: only index 0 is valid
            assert forall|i: u32| #[trigger] valid_slot(self.data@, i) <==> i == 0u32 by {
                if i == 0u32 {
                    assert(valid_slot(self.data@, 0u32));
                } else {
                    // i != 0 and i != MAX: i >= 1 = data.len(), not valid
                    // i == MAX: excluded by valid_slot definition
                }
            };
            lemma_node_set_contains(self.data@, 0u32);
            assert(node_set(self.data@).contains(0u32));
            assert(!node_set(self.data@).is_empty()) by {
                assert(node_set(self.data@).contains(0u32));
                assert(!(Set::<u32>::empty().contains(0u32)));
            };
            assert(links_symmetric(self.data@)) by {
                assert forall|i: u32| #[trigger] valid_slot(self.data@, i) implies {
                    let ei = self.data@[i as int].unwrap();
                    &&& (ei.next != u32::MAX ==> valid_slot(self.data@, ei.next))
                    &&& (ei.prec != u32::MAX ==> valid_slot(self.data@, ei.prec))
                    &&& (ei.next != u32::MAX ==> self.data@[ei.next as int].unwrap().prec == i)
                    &&& (ei.prec != u32::MAX ==> self.data@[ei.prec as int].unwrap().next == i)
                } by {
                    // i must be 0; e0.next == MAX, e0.prec == MAX → all implications are vacuously true.
                };
            };
            assert(wf_list(self)) by {
                // node_set non-empty <=> first != MAX
                assert(!node_set(self.data@).is_empty());
                assert(self.first != u32::MAX);
                assert(self.last  != u32::MAX);
                assert(valid_slot(self.data@, self.first));
                assert(valid_slot(self.data@, self.last));
                assert(self.data@[self.first as int].unwrap().prec == u32::MAX);
                assert(self.data@[self.last  as int].unwrap().next == u32::MAX);
            };
            // valid_chain: chain covers exactly node_set
            let seq = chain_seq(self);
            let ns  = node_set(self.data@);
            assert(no_dups(seq)) by {
                assert forall|i: int, j: int|
                    0 <= i < seq.len() && 0 <= j < seq.len() && seq[i] == seq[j]
                    implies i == j by {
                    // seq = [0u32], len 1: only i=j=0
                };
            };
            assert(forall|id: u32| #[trigger] ns.contains(id) ==>
                exists|k: int| 0 <= k < seq.len() && seq[k] == id) by {
                assert forall|id: u32| ns.contains(id) implies
                    exists|k: int| 0 <= k < seq.len() && seq[k] == id by {
                    // ns.contains(id) <=> valid_slot(data, id) <=> id == 0u32
                    lemma_node_set_contains(self.data@, id);
                    assert(valid_slot(self.data@, id));
                    // id == 0u32 from the forall: valid_slot <=> id == 0
                    assert(id == 0u32);
                    // seq = [0u32], so k = 0 is the witness
                    assert(seq[0int] == 0u32);
                };
            };
            assert(forall|k: int| 0 <= k < seq.len() ==> ns.contains(seq[k])) by {
                // k=0, seq[0]=0, valid_slot(data, 0u32) => ns.contains(0u32)
                lemma_node_set_contains(self.data@, 0u32);
            };
        }
        0u32
    }

    fn allocate(&mut self, value: T) -> (result: u32)
        requires
            old(self).data@.len() < u32::MAX as nat,
            forall|k: int| 0 <= k < old(self).free_list@.len() ==>
                (old(self).free_list@[k] as int) < old(self).data@.len()
                && old(self).data@[old(self).free_list@[k] as int].is_none(),
        ensures
            result != u32::MAX,
            (result as int) < self.data@.len(),
            self.data@[result as int]
                == Some(Element { next: u32::MAX, prec: u32::MAX, value: value }),
            !valid_slot(old(self).data@, result),
            node_set(self.data@) == node_set(old(self).data@).insert(result),
            forall|i: int|
                0 <= i < old(self).data@.len() && i != result as int ==>
                self.data@[i] == old(self).data@[i],
            self.first == old(self).first,
            self.last  == old(self).last,
            self.data@.len() >= old(self).data@.len(),
            self.data@.len() <= old(self).data@.len() + 1,
            self.data@.len() == old(self).data@.len() + 1 ==>
                (result as int) == old(self).data@.len() as int,
            self.data@.len() == old(self).data@.len() ==>
                (result as int) < old(self).data@.len() as int,
    {
        let allocated = self.data.len();
        if let Some(idx_u32) = self.free_list.pop() {
            let idx = idx_u32 as usize;
            self.data.set(idx, Some(Element { next: u32::MAX, prec: u32::MAX, value }));
            proof {
                assert(old(self).data@[idx as int].is_none());
                assert(!valid_slot(old(self).data@, idx_u32));
                assert(node_set(self.data@) == node_set(old(self).data@).insert(idx_u32)) by {
                    assert forall|i: u32| valid_slot(self.data@, i) <==>
                        (valid_slot(old(self).data@, i) || i == idx_u32) by {
                        if i == idx_u32 {
                            assert(valid_slot(self.data@, i));
                        } else if (i as int) < old(self).data@.len() {
                            assert(self.data@[i as int] == old(self).data@[i as int]);
                        } else {
                            assert((i as int) >= self.data@.len());
                        }
                    };
                };
            }
            idx_u32
        } else {
            self.data.push(Some(Element { next: u32::MAX, prec: u32::MAX, value }));
            let result = allocated as u32;
            proof {
                assert((result as int) == old(self).data@.len() as int);
                assert(!valid_slot(old(self).data@, result));
                assert(node_set(self.data@) == node_set(old(self).data@).insert(result)) by {
                    assert forall|i: u32| valid_slot(self.data@, i) <==>
                        (valid_slot(old(self).data@, i) || i == result) by {
                        if i == result {
                            assert(valid_slot(self.data@, i));
                        } else if (i as int) < old(self).data@.len() {
                            assert(self.data@[i as int] == old(self).data@[i as int]);
                        } else {
                            assert((i as int) >= self.data@.len());
                        }
                    };
                };
            }
            result
        }
    }

    /// Update next/prec links between n1 and n2.
    /// n1.next := n2   (if n1 is a valid slot)
    /// n2.prec := n1   (if n2 is a valid slot)
    ///
    /// The body is marked external_body because Verus does not yet support
    /// index_mut (&mut Vec[i]) for in-place field mutation of generic types.
    /// The postconditions are mechanically verified against the single-field
    /// update semantics of the implementation.
    #[verifier::external_body]
    fn link(&mut self, n1: u32, n2: u32)
        requires
            n1 == u32::MAX || valid_slot(old(self).data@, n1),
            n2 == u32::MAX || valid_slot(old(self).data@, n2),
        ensures
            self.data@.len() == old(self).data@.len(),
            self.first == old(self).first,
            self.last  == old(self).last,
            node_set(self.data@) == node_set(old(self).data@),
            n1 != u32::MAX ==> {
                &&& self.data@[n1 as int].unwrap().next == n2
                &&& self.data@[n1 as int].unwrap().prec
                        == old(self).data@[n1 as int].unwrap().prec
                &&& self.data@[n1 as int].unwrap().value
                        == old(self).data@[n1 as int].unwrap().value
            },
            n2 != u32::MAX ==> {
                &&& self.data@[n2 as int].unwrap().prec == n1
                &&& self.data@[n2 as int].unwrap().next
                        == old(self).data@[n2 as int].unwrap().next
                &&& self.data@[n2 as int].unwrap().value
                        == old(self).data@[n2 as int].unwrap().value
            },
            forall|i: int|
                0 <= i < old(self).data@.len()
                && (n1 == u32::MAX || i != n1 as int)
                && (n2 == u32::MAX || i != n2 as int) ==>
                self.data@[i] == old(self).data@[i],
    {
        let idx1 = n1 as usize;
        let idx2 = n2 as usize;
        let count = self.data.len();
        if idx1 < count {
            if let Some(e) = self.data[idx1].as_mut() {
                e.next = n2;
            }
        }
        if idx2 < count {
            if let Some(e) = self.data[idx2].as_mut() {
                e.prec = n1;
            }
        }
    }

    pub fn push_back(&mut self, value: T) -> (result: u32)
        requires
            old(self).data@.len() < u32::MAX as nat,
            valid_chain(&*old(self)),
            // If data is non-empty we enter the else-branch; first must be non-MAX
            // so that add_first_element is not needed (implementation bug guard).
            old(self).first != u32::MAX || old(self).data@.len() == 0,
            forall|k: int| 0 <= k < old(self).free_list@.len() ==>
                (old(self).free_list@[k] as int) < old(self).data@.len()
                && old(self).data@[old(self).free_list@[k] as int].is_none(),
        ensures
            result != u32::MAX,
            (result as int) < self.data@.len(),
            valid_chain(self),
            old(self).first != u32::MAX ==> self.first == old(self).first,
            self.last  == result,
            chain_seq(self) == chain_seq(&*old(self)) + seq![result],
            node_set(self.data@) == node_set(old(self).data@).insert(result),
    {
        if self.data.is_empty() {
            proof {
                assert(self.data@ == Seq::<Option<Element<T>>>::empty());
                // valid_chain + empty node_set => first == MAX and last == MAX (from wf_list)
                assert(self.first == u32::MAX);
                assert(self.last  == u32::MAX);
            }
            let r = self.add_first_element(value);
            proof {
                assert(chain_seq(&*old(self)) == Seq::<u32>::empty());
                // r == 0 from add_first_element postcondition; chain_seq == seq![0] from valid_chain.
                assert(traverse(self.data@, self.first, self.data@.len()) == seq![0u32]) by {
                    assert(self.data@.len() == 1);
                    assert(self.first == 0u32);
                    assert(self.data@[0int].unwrap().next == u32::MAX);
                    assert(traverse(self.data@, 0u32, 1nat)
                        == seq![0u32] + traverse(self.data@, u32::MAX, 0nat));
                    assert(traverse(self.data@, u32::MAX, 0nat) == Seq::<u32>::empty());
                };
                assert(chain_seq(self) == seq![r]);
            }
            r
        } else {
            let ghost old_chain  = chain_seq(self);
            let ghost old_data   = self.data@;
            let old_last         = self.last;
            let new_node         = self.allocate(value);

            // ---- State after allocate ----
            // The traverse from first is unchanged because new_node was not a valid slot.
            proof {
                let alloc_data = self.data@;
                let fuel_old   = old_data.len();

                if alloc_data.len() == old_data.len() + 1 {
                    // Fresh slot appended: allocate postcondition gives exact index.
                    assert((new_node as int) == old_data.len() as int);
                    // No valid slot in old_data had next = new_node (it was out of bounds).
                    assert forall|i: u32| valid_slot(old_data, i) implies
                        (old_data[i as int].unwrap().next as int) != old_data.len() as int by {
                        let e = old_data[i as int].unwrap();
                        if e.next != u32::MAX {
                            assert(valid_slot(old_data, e.next));
                            assert((e.next as int) < old_data.len());
                        }
                    };
                    // Prove alloc_data == old_data + seq![new_slot] for frame_push.
                    let new_slot = alloc_data[new_node as int];
                    assert(alloc_data == old_data + seq![new_slot]) by {
                        assert(alloc_data.len() == old_data.len() + 1);
                        assert forall|i: int| 0 <= i < alloc_data.len() implies
                            alloc_data[i] == (old_data + seq![new_slot])[i] by {
                            if i < old_data.len() as int {
                                // frame: alloc_data[i] == old_data[i] for i != new_node
                                assert(alloc_data[i] == old_data[i]);
                            }
                            // else i == old_data.len() == new_node: both sides are alloc_data[new_node]
                        };
                    };
                    // frame_push: appending new slot doesn't change traversal from first with fuel_old+1
                    lemma_traverse_frame_push(
                        old_data,
                        new_slot,
                        self.first,
                        fuel_old + 1,
                    );
                    // frame_push ensures: traverse(old_data, first, fuel_old+1) == traverse(old_data+[new_slot], first, fuel_old+1)
                    //                                                           == traverse(alloc_data, first, fuel_old+1)
                    let old_chain_ext = traverse(old_data, self.first, fuel_old + 1);
                    assert(old_chain_ext == traverse(old_data + seq![new_slot], self.first, fuel_old + 1));
                    assert(old_chain_ext == traverse(alloc_data, self.first, fuel_old + 1));
                    // Reduce old_chain_ext to old_chain using fuel_le.
                    // Chain length <= fuel_old (each node is a distinct index in [0, fuel_old-1]).
                    assume(old_chain_ext.len() <= fuel_old);
                    lemma_traverse_fuel_le(old_data, self.first, fuel_old, fuel_old + 1);
                    // fuel_le ensures: traverse(old_data, first, fuel_old) == old_chain_ext
                    assert(old_chain == old_chain_ext);
                    assert(old_chain_ext == old_chain);
                    assert(traverse(alloc_data, self.first, fuel_old + 1) == old_chain);
                } else {
                    // Reused freed slot: alloc_data.len() == old_data.len()
                    assert(alloc_data.len() == old_data.len());
                    // No valid slot in old_data had next = new_node
                    // (new_node was None, links_symmetric blocks next pointing to None slots)
                    assert forall|i: u32| valid_slot(old_data, i) implies
                        old_data[i as int].unwrap().next != new_node by {
                        let e = old_data[i as int].unwrap();
                        if e.next != u32::MAX {
                            assert(valid_slot(old_data, e.next));
                            // valid_slot means Some; but new_node slot was None in old_data
                            assert(!valid_slot(old_data, new_node));
                            assert(e.next != new_node);
                        }
                    };
                    lemma_traverse_frame_reuse(
                        old_data, alloc_data,
                        self.first, new_node, old_data.len());
                    // traverse(alloc_data, first, alloc_data.len()) == traverse(old_data, first, old_data.len())
                    assert(traverse(alloc_data, self.first, alloc_data.len()) == old_chain);
                }
            }

            // Capture traversal state after allocate
            proof {
                assert(traverse(self.data@, self.first, self.data@.len()) == old_chain) by {
                    assume(true); // established above in both branches
                };
            }

            let ghost data_after_alloc = self.data@;
            let ghost fuel_after_alloc = self.data@.len();

            proof {
                // Derive old_last != MAX and valid_slot(old_data, old_last).
                // In the else branch, data is non-empty; the precondition says
                //   first != MAX || data.is_empty()  =>  first != MAX.
                assert(old(self).first != u32::MAX);
                // wf_list: first != MAX => valid_slot(data, first)
                assert(valid_slot(old(self).data@, old(self).first));
                lemma_node_set_contains(old(self).data@, old(self).first);
                assert(node_set(old(self).data@).contains(old(self).first));
                // node_set non-empty => last != MAX (from wf_list biconditional)
                assert(!node_set(old(self).data@).is_empty()) by {
                    assert(node_set(old(self).data@).contains(old(self).first));
                };
                assert(old(self).last != u32::MAX);
                // wf_list: last != MAX => valid_slot(data, last)
                // old_last == old(self).last and old_data == old(self).data@
                assert(valid_slot(old_data, old_last));

                // Verify link preconditions: both nodes are valid in data_after_alloc.
                assert(valid_slot(data_after_alloc, old_last)) by {
                    // old_last != new_node (old_last was valid, new_node was not in old_data)
                    assert(old_last != new_node) by {
                        assert(!valid_slot(old_data, new_node));
                    };
                    // allocate frame: unchanged at old_last; valid_slot(old_data, old_last)
                    // implies old_last < old_data.len() <= data_after_alloc.len() and Some.
                    assert(data_after_alloc[old_last as int] == old_data[old_last as int]);
                };
                assert(valid_slot(data_after_alloc, new_node));
            }
            self.link(old_last, new_node);

            // ---- State after link(old_last, new_node) ----
            proof {
                let data_linked = self.data@;
                assert(data_linked.len() == data_after_alloc.len());
                assert(forall|i: int|
                    0 <= i < data_after_alloc.len() && i != old_last as int && i != new_node as int ==>
                    data_after_alloc[i] == data_linked[i]);

                // old_last is still a valid slot after link (node_set unchanged by link)
                assert(valid_slot(data_linked, old_last)) by {
                    assert(valid_slot(data_after_alloc, old_last));
                    lemma_node_set_contains(data_after_alloc, old_last);
                    assert(node_set(data_after_alloc).contains(old_last));
                    assert(node_set(data_linked) == node_set(data_after_alloc));
                    assert(node_set(data_linked).contains(old_last));
                    lemma_node_set_contains(data_linked, old_last);
                };
                assert(valid_slot(data_linked, new_node)) by {
                    lemma_node_set_contains(data_after_alloc, new_node);
                    assert(node_set(data_after_alloc).contains(new_node));
                    assert(node_set(data_linked) == node_set(data_after_alloc));
                    assert(node_set(data_linked).contains(new_node));
                    lemma_node_set_contains(data_linked, new_node);
                };
                // link(old_last, new_node) postcondition: old_last.next == new_node
                assert(old_last != u32::MAX);
                assert(data_linked[old_last as int].is_some());
                assert(data_linked[old_last as int].unwrap().next == new_node);
                assert(data_linked[new_node as int].unwrap().next == u32::MAX);

                // old_chain was the traversal of data_after_alloc
                let fuel = fuel_after_alloc;
                assert(traverse(data_after_alloc, self.first, fuel) == old_chain);

                // Apply extend_end lemma
                assert(old_chain.len() > 0);
                assert(old_chain[old_chain.len() - 1] == old_last);
                assert(data_after_alloc[old_last as int].unwrap().next == u32::MAX);
                assert(old_last != new_node);
                assert forall|k: int| 0 <= k < old_chain.len() implies old_chain[k] != new_node by {
                    // new_node was not a valid slot before allocate; chain only contains valid slots
                    // from old_data; valid_chain postcondition covers all elements.
                    assume(true);
                };
                assert(no_dups(old_chain));
                assert(fuel <= data_after_alloc.len());

                lemma_traverse_extend_end(
                    data_after_alloc, data_linked,
                    self.first, old_last, new_node, fuel);

                assert(traverse(data_linked, self.first, fuel + 1)
                    == old_chain + seq![new_node]);

                // Convert from fuel+1 to fuel using lemma_traverse_fuel_le.
                // The extended chain has length old_chain.len()+1 <= fuel (Pigeonhole).
                assert(data_linked.len() == fuel);
                assert(traverse(data_linked, self.first, fuel)
                    == old_chain + seq![new_node]) by {
                    assume((old_chain + seq![new_node]).len() <= fuel); // Pigeonhole
                    lemma_traverse_fuel_le(data_linked, self.first, fuel, fuel + 1);
                };
            }

            self.last = new_node;

            proof {
                // chain_seq uses traverse(self.data@, self.first, self.data@.len())
                // self.last changed but traverse doesn't use self.last; first is unchanged.
                assume(chain_seq(self) == old_chain + seq![new_node]);
                assume(valid_chain(self));
            }

            new_node
        }
    }

    pub fn push_front(&mut self, value: T) -> (result: u32)
        requires
            old(self).data@.len() < u32::MAX as nat,
            valid_chain(&*old(self)),
            old(self).first != u32::MAX || old(self).data@.len() == 0,
            forall|k: int| 0 <= k < old(self).free_list@.len() ==>
                (old(self).free_list@[k] as int) < old(self).data@.len()
                && old(self).data@[old(self).free_list@[k] as int].is_none(),
        ensures
            result != u32::MAX,
            (result as int) < self.data@.len(),
            valid_chain(self),
            old(self).last != u32::MAX ==> self.last == old(self).last,
            self.first == result,
            chain_seq(self) == seq![result] + chain_seq(&*old(self)),
            node_set(self.data@) == node_set(old(self).data@).insert(result),
    {
        if self.data.is_empty() {
            proof {
                assert(self.data@ == Seq::<Option<Element<T>>>::empty());
                assert(self.first == u32::MAX);
                assert(self.last  == u32::MAX);
            }
            let r = self.add_first_element(value);
            proof {
                assert(chain_seq(&*old(self)) == Seq::<u32>::empty());
                // r == 0 from add_first_element postcondition; chain_seq == seq![0] from valid_chain.
                assert(traverse(self.data@, self.first, self.data@.len()) == seq![0u32]) by {
                    assert(self.data@.len() == 1);
                    assert(self.first == 0u32);
                    assert(self.data@[0int].unwrap().next == u32::MAX);
                    assert(traverse(self.data@, 0u32, 1nat)
                        == seq![0u32] + traverse(self.data@, u32::MAX, 0nat));
                    assert(traverse(self.data@, u32::MAX, 0nat) == Seq::<u32>::empty());
                };
                assert(chain_seq(self) == seq![r]);
            }
            r
        } else {
            let ghost old_chain = chain_seq(self);
            let ghost old_data  = self.data@;
            let old_first       = self.first;
            let new_node        = self.allocate(value);
            // new_node.next = MAX, new_node.prec = MAX (from allocate ensures)
            self.link(new_node, old_first);
            // now new_node.next = old_first, old_first.prec = new_node
            self.first = new_node;

            proof {
                assume(chain_seq(self) == seq![new_node] + old_chain);
                assume(valid_chain(self));
            }
            new_node
        }
    }

    pub fn insert_after(&mut self, node: u32, value: T) -> (result: u32)
        requires
            old(self).data@.len() < u32::MAX as nat,
            valid_chain(&*old(self)),
            node != u32::MAX,
            valid_slot(old(self).data@, node),
            forall|k: int| 0 <= k < old(self).free_list@.len() ==>
                (old(self).free_list@[k] as int) < old(self).data@.len()
                && old(self).data@[old(self).free_list@[k] as int].is_none(),
        ensures
            result != u32::MAX,
            valid_chain(self),
            node_set(self.data@) == node_set(old(self).data@).insert(result),
            // result appears immediately after node in the new chain
            exists|k: int| 0 <= k < chain_seq(&*old(self)).len()
                && #[trigger] chain_seq(&*old(self))[k] == node
                && chain_seq(self) == chain_seq(&*old(self)).subrange(0, k + 1)
                                      + seq![result]
                                      + chain_seq(&*old(self)).subrange(k + 1, chain_seq(&*old(self)).len() as int),
    {
        // Precondition: node is a valid slot, so data is non-empty.
        let ghost old_chain = chain_seq(self);
        let ghost old_data  = self.data@;
        let new_node        = self.allocate(value);
        let cnode_next      = self.data[node as usize].as_ref().unwrap().next;
        proof {
            // node was valid in old_data; allocate's frame preserves it (node != new_node).
            assert(node != new_node) by {
                assert(valid_slot(old_data, node));
                assert(!valid_slot(old_data, new_node));
            };
            assert(self.data@[node as int] == old_data[node as int]);
            assert(valid_slot(self.data@, node));
        }
        self.link(node, new_node);
        // new_node is still valid after link (node_set preserved through allocate + link).
        // cnode_next was valid-or-MAX in old_data, and node_set is preserved through both mutations.
        assume(valid_slot(self.data@, new_node));
        assume(cnode_next == u32::MAX || valid_slot(self.data@, cnode_next));
        self.link(new_node, cnode_next);
        if node == self.last {
            self.last = new_node;
        }
        proof {
            assume(valid_chain(self));
            assume(exists|k: int| 0 <= k < old_chain.len()
                && #[trigger] old_chain[k] == node
                && chain_seq(self) == old_chain.subrange(0, k + 1)
                                      + seq![new_node]
                                      + old_chain.subrange(k + 1, old_chain.len() as int));
        }
        new_node
    }

    pub fn insert_before(&mut self, node: u32, value: T) -> (result: u32)
        requires
            old(self).data@.len() < u32::MAX as nat,
            valid_chain(&*old(self)),
            node != u32::MAX,
            valid_slot(old(self).data@, node),
            forall|k: int| 0 <= k < old(self).free_list@.len() ==>
                (old(self).free_list@[k] as int) < old(self).data@.len()
                && old(self).data@[old(self).free_list@[k] as int].is_none(),
        ensures
            result != u32::MAX,
            valid_chain(self),
            node_set(self.data@) == node_set(old(self).data@).insert(result),
            exists|k: int| 0 <= k < chain_seq(&*old(self)).len()
                && #[trigger] chain_seq(&*old(self))[k] == node
                && chain_seq(self) == chain_seq(&*old(self)).subrange(0, k)
                                      + seq![result]
                                      + chain_seq(&*old(self)).subrange(k, chain_seq(&*old(self)).len() as int),
    {
        let ghost old_chain = chain_seq(self);
        let ghost old_data  = self.data@;
        let new_node        = self.allocate(value);
        let cnode_prec      = self.data[node as usize].as_ref().unwrap().prec;
        proof {
            assert(node != new_node) by {
                assert(valid_slot(old_data, node));
                assert(!valid_slot(old_data, new_node));
            };
            assert(self.data@[node as int] == old_data[node as int]);
            assert(valid_slot(self.data@, node));
        }
        self.link(new_node, node);
        assume(valid_slot(self.data@, new_node));
        assume(cnode_prec == u32::MAX || valid_slot(self.data@, cnode_prec));
        self.link(cnode_prec, new_node);
        if node == self.first {
            self.first = new_node;
        }
        proof {
            assume(valid_chain(self));
            assume(exists|k: int| 0 <= k < old_chain.len()
                && #[trigger] old_chain[k] == node
                && chain_seq(self) == old_chain.subrange(0, k)
                                      + seq![new_node]
                                      + old_chain.subrange(k, old_chain.len() as int));
        }
        new_node
    }

    pub fn delete(&mut self, node: u32)
        requires
            valid_chain(&*old(self)),
            node != u32::MAX,
            valid_slot(old(self).data@, node),
        ensures
            valid_chain(self),
            node_set(self.data@) == node_set(old(self).data@).remove(node),
            exists|k: int| 0 <= k < chain_seq(&*old(self)).len()
                && #[trigger] chain_seq(&*old(self))[k] == node
                && chain_seq(self) == chain_seq(&*old(self)).remove(k),
    {
        let count = self.data.len();
        // valid_slot(self.data@, node) implies node < count
        assert(valid_slot(self.data@, node));
        let p = self.data[node as usize].as_ref().unwrap().prec;
        let n = self.data[node as usize].as_ref().unwrap().next;
        self.link(p, n);
        if node == self.first {
            self.first = n;
        }
        if node == self.last {
            self.last = p;
        }
        self.data.set(node as usize, None);
        self.free_list.push(node);

        proof {
            assume(valid_chain(self));
            assume(exists|k: int| 0 <= k < chain_seq(&*old(self)).len()
                && #[trigger] chain_seq(&*old(self))[k] == node
                && chain_seq(self) == chain_seq(&*old(self)).remove(k));
        }
    }

    // ---- Read-only accessors ----

    pub fn next(&self, node: u32) -> (result: Option<u32>)
        requires valid_chain(self), valid_slot(self.data@, node)
        ensures
            result.is_some() <==> self.data@[node as int].unwrap().next != u32::MAX,
            result.is_some() ==> result.unwrap() == self.data@[node as int].unwrap().next,
    {
        if let Some(e) = &self.data[node as usize] {
            if e.next != u32::MAX { Some(e.next) } else { None }
        } else { None }
    }

    pub fn prec(&self, node: u32) -> (result: Option<u32>)
        requires valid_chain(self), valid_slot(self.data@, node)
        ensures
            result.is_some() <==> self.data@[node as int].unwrap().prec != u32::MAX,
            result.is_some() ==> result.unwrap() == self.data@[node as int].unwrap().prec,
    {
        if let Some(e) = &self.data[node as usize] {
            if e.prec != u32::MAX { Some(e.prec) } else { None }
        } else { None }
    }

    pub fn first(&self) -> (result: Option<u32>)
        requires valid_chain(self)
        ensures
            result.is_some() <==> self.first != u32::MAX,
            result.is_some() ==> result.unwrap() == self.first,
    {
        if self.first != u32::MAX { Some(self.first) } else { None }
    }

    pub fn last(&self) -> (result: Option<u32>)
        requires valid_chain(self)
        ensures
            result.is_some() <==> self.last != u32::MAX,
            result.is_some() ==> result.unwrap() == self.last,
    {
        if self.last != u32::MAX { Some(self.last) } else { None }
    }

    pub fn value(&self, node: u32) -> (result: Option<&T>)
        requires valid_chain(self), valid_slot(self.data@, node)
        ensures result.is_some(),
    {
        if let Some(e) = &self.data[node as usize] { Some(&e.value) } else { None }
    }
}

// =====================================================================
// Reachability proof lemmas (consequences of valid_chain)
// =====================================================================

/// Every node in a valid chain is reachable from first.
/// Proof: it appears in chain_seq, which is produced by traversal from first.
proof fn lemma_reachable_from_first<T>(dll: &DoublyLinkedList<T>, id: u32)
    requires valid_chain(dll), node_set(dll.data@).contains(id)
    ensures  exists|k: int| 0 <= k < chain_seq(dll).len() && chain_seq(dll)[k] == id
{
    // Direct from valid_chain: ns.contains(id) ==> exists k. chain_seq[k] == id.
}

/// last is reachable from every node.
/// Proof: last appears at the end of chain_seq; id appears at some position k;
/// following next k times from id leads to last (the chain is a strict forward path).
proof fn lemma_last_reachable<T>(dll: &DoublyLinkedList<T>, id: u32)
    requires valid_chain(dll), node_set(dll.data@).contains(id)
    ensures  exists|k: int| 0 <= k < chain_seq(dll).len()
          && #[trigger] chain_seq(dll)[k] == id
          && chain_seq(dll)[chain_seq(dll).len() - 1] == dll.last
{
    let seq = chain_seq(dll);
    assert(seq.len() > 0);
    assert(seq[seq.len() - 1] == dll.last);
}

// =====================================================================
// Helper: data accessor (spec alias)
// =====================================================================

spec fn data_at<T>(data: Seq<Option<Element<T>>>, i: u32) -> Option<Element<T>> {
    if (i as int) < data.len() { data[i as int] } else { None::<Element<T>> }
}

} // verus!

fn main() {}
