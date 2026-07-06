// Verus specification for an index-based Doubly Linked List.
//
// Source implementation: index_impl.rs:1-230
// Target property:        reachability-based chain validity
//
// Chain validity (per the reachability definition):
//   * every existing node is reachable from `first` by following `next`, and
//   * from every existing node, `last` is reachable by following `next`.
//
// Structures are preserved from the implementation (the allocator + lifetime
// from `Vec<_, &'x TheAlloc>` are dropped, as allowed by the simplified
// structure rule; the concrete fields data/free_list/first/last are kept).

use vstd::prelude::*;

verus! {

// u32::MAX is the "null"/sentinel handle used by the implementation.
pub const NULL: u32 = 0xFFFF_FFFF; // == u32::MAX

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

impl<T> DoublyLinkedList<T> {
    // ---- Abstract view over the concrete storage -------------------------

    // A handle refers to a live node iff it is in range and its slot is Some.
    pub open spec fn node_exists(&self, id: u32) -> bool {
        0 <= id < self.data@.len() && self.data@[id as int].is_some()
    }

    pub open spec fn elem(&self, id: u32) -> Element<T>
        recommends self.node_exists(id),
    {
        self.data@[id as int]->Some_0
    }

    // Abstract successor: None at the sentinel or for non-nodes.
    pub open spec fn next_of(&self, id: u32) -> Option<u32> {
        if self.node_exists(id) && self.elem(id).next != NULL {
            Some(self.elem(id).next)
        } else {
            None
        }
    }

    // Abstract predecessor.
    pub open spec fn prec_of(&self, id: u32) -> Option<u32> {
        if self.node_exists(id) && self.elem(id).prec != NULL {
            Some(self.elem(id).prec)
        } else {
            None
        }
    }

    // ---- Reachability ----------------------------------------------------

    // `reaches(src, dst, fuel)`: dst is reachable from src in <= fuel hops of
    // `next`. `fuel` is a termination measure (a node count bound).
    pub open spec fn reaches(&self, src: u32, dst: u32, fuel: nat) -> bool
        decreases fuel,
    {
        if src == dst {
            true
        } else if fuel == 0 {
            false
        } else {
            match self.next_of(src) {
                Some(n) => self.reaches(n, dst, (fuel - 1) as nat),
                None => false,
            }
        }
    }

    // Reachability: some finite number of `next` steps connects src to dst.
    pub open spec fn reachable(&self, src: u32, dst: u32) -> bool {
        exists|fuel: nat| self.reaches(src, dst, fuel)
    }

    // ---- Structural well-formedness (link consistency) -------------------

    pub open spec fn links_consistent(&self) -> bool {
        forall|id: u32| #[trigger] self.node_exists(id) ==> {
            &&& (self.next_of(id).is_some() ==> self.node_exists(self.next_of(id).unwrap()))
            &&& (self.prec_of(id).is_some() ==> self.node_exists(self.prec_of(id).unwrap()))
            &&& (self.next_of(id).is_some() ==> self.prec_of(self.next_of(id).unwrap()) == Some(id))
            &&& (self.prec_of(id).is_some() ==> self.next_of(self.prec_of(id).unwrap()) == Some(id))
        }
    }

    pub open spec fn endpoints_wf(&self) -> bool {
        &&& (self.first == NULL <==> self.last == NULL)
        &&& (self.first != NULL ==> self.node_exists(self.first))
        &&& (self.last != NULL ==> self.node_exists(self.last))
        &&& (self.first != NULL ==> self.prec_of(self.first).is_none())
        &&& (self.last != NULL ==> self.next_of(self.last).is_none())
    }

    // ---- The target property: reachability-based chain validity ----------

    pub open spec fn reachable_from_first(&self) -> bool {
        forall|id: u32| #[trigger] self.node_exists(id) ==> self.reachable(self.first, id)
    }

    pub open spec fn reaches_last(&self) -> bool {
        forall|id: u32| #[trigger] self.node_exists(id) ==> self.reachable(id, self.last)
    }

    pub open spec fn valid_chain(&self) -> bool {
        &&& self.endpoints_wf()
        &&& self.links_consistent()
        &&& self.reachable_from_first()
        &&& self.reaches_last()
    }

    // ---- Free-list well-formedness --------------------------------------
    //
    // The allocator reuses slots recorded in `free_list`. For `allocate` to be
    // correct (never clobber a live node), every recorded index must point at a
    // genuine hole (a `None` slot in range) and the indices must be distinct.
    // `delete` is what maintains this; we model it so `allocate` has a sound
    // contract instead of an unchecked `unwrap`.
    pub open spec fn free_list_wf(&self) -> bool {
        &&& (forall|i: int|
                0 <= i < self.free_list@.len() ==> {
                    let f = #[trigger] self.free_list@[i];
                    &&& 0 <= f < self.data@.len()
                    &&& self.data@[f as int].is_none()
                })
        &&& (forall|i: int, j: int|
                0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() && i != j
                    ==> self.free_list@[i] != self.free_list@[j])
    }

    // The full structural invariant maintained by the (correct) operations:
    // a valid reachability chain plus a well-formed free list.
    pub open spec fn wf(&self) -> bool {
        &&& self.valid_chain()
        &&& self.free_list_wf()
    }
}

// ===========================================================================
// Reachability lemmas (proven, used as the proof toolkit for the property)
// ===========================================================================

impl<T> DoublyLinkedList<T> {
    // A node reaches itself with zero fuel.
    pub proof fn lemma_reaches_self(&self, id: u32)
        ensures self.reaches(id, id, 0),
    {
        // src == dst branch of `reaches` is immediate.
    }

    // Therefore every node is reachable from itself.
    pub proof fn lemma_reachable_self(&self, id: u32)
        ensures self.reachable(id, id),
    {
        self.lemma_reaches_self(id);
        assert(self.reaches(id, id, 0));
    }

    // Monotonicity in fuel: more fuel never loses reachability.
    pub proof fn lemma_reaches_fuel_mono(&self, src: u32, dst: u32, f: nat, g: nat)
        requires self.reaches(src, dst, f), f <= g,
        ensures self.reaches(src, dst, g),
        decreases f,
    {
        if src == dst {
            // reaches(_, _, g) holds for any g via the src == dst branch.
        } else {
            // f > 0 here (else reaches(src,dst,f) would be false), and g > 0.
            match self.next_of(src) {
                Some(n) => {
                    self.lemma_reaches_fuel_mono(n, dst, (f - 1) as nat, (g - 1) as nat);
                }
                None => {}
            }
        }
    }

    // One forward `next` step prepended to a path stays a path.
    pub proof fn lemma_reaches_step(&self, src: u32, mid: u32, dst: u32, f: nat)
        requires
            self.next_of(src) == Some(mid),
            self.reaches(mid, dst, f),
        ensures
            self.reaches(src, dst, f + 1),
    {
        if src == dst {
            // immediate
        } else {
            // unfold reaches(src, dst, f+1): next_of(src) == Some(mid), and
            // reaches(mid, dst, (f+1)-1) == reaches(mid, dst, f) holds.
            assert(self.reaches(src, dst, f + 1) == self.reaches(mid, dst, f));
        }
    }

    // One forward `next` step APPENDED to the end of a path stays a path:
    // if src reaches b, and b -> c, then src reaches c (with one more hop).
    pub proof fn lemma_reaches_append(&self, a: u32, b: u32, c: u32, f: nat)
        requires
            self.reaches(a, b, f),
            self.next_of(b) == Some(c),
        ensures
            self.reaches(a, c, f + 1),
        decreases f,
    {
        if a == b {
            assert(self.next_of(a) == Some(c));
            assert(self.reaches(c, c, f));
        } else {
            assert(self.next_of(a).is_some());
            let m = self.next_of(a).unwrap();
            assert(self.reaches(m, b, (f - 1) as nat));
            self.lemma_reaches_append(m, b, c, (f - 1) as nat);
        }
    }

    // Two-state frame lemma. If `pre` and `post` agree on `next_of` everywhere
    // except at a node `k` that had NO successor in `pre`, then every pre-path
    // survives unchanged into `post`. This is exactly the shape of a push to the
    // end (k = old last) or a prepend (k = the fresh node, absent in `pre`):
    // the only changed `next` belongs to a node that previously dead-ended, so
    // no existing path could have stepped through it.
    pub proof fn lemma_frame_noext(
        pre: &DoublyLinkedList<T>,
        post: &DoublyLinkedList<T>,
        k: u32,
        a: u32,
        b: u32,
        f: nat,
    )
        requires
            forall|id: u32| pre.next_of(id) == post.next_of(id) || id == k,
            pre.next_of(k).is_none(),
            pre.reaches(a, b, f),
        ensures
            post.reaches(a, b, f),
        decreases f,
    {
        if a == b {
        } else {
            let m = pre.next_of(a).unwrap();
            assert(pre.next_of(a).is_some());
            assert(a != k);
            assert(post.next_of(a) == pre.next_of(a));
            Self::lemma_frame_noext(pre, post, k, m, b, (f - 1) as nat);
        }
    }

    // Two-state SPLICE lemma. `post` inserts a fresh node `nw` immediately after
    // `nd`: nd -> nw -> (nd's old successor), with all other next-links equal.
    // Then every pre-path survives, costing at most one extra hop per step (the
    // 2*f+2 bound generously absorbs the inserted node). This is the reachability
    // engine for insert_after / insert_before.
    pub proof fn lemma_reaches_splice(
        pre: &DoublyLinkedList<T>,
        post: &DoublyLinkedList<T>,
        nd: u32,
        nw: u32,
        a: u32,
        b: u32,
        f: nat,
    )
        requires
            forall|id: u32| id != nd && id != nw ==> pre.next_of(id) == post.next_of(id),
            post.next_of(nd) == Some(nw),
            post.next_of(nw) == pre.next_of(nd),
            !pre.node_exists(nw),
            pre.reaches(a, b, f),
        ensures
            post.reaches(a, b, 2 * f + 2),
        decreases f,
    {
        if a == b {
            // post.reaches(a, a, _) is immediate.
        } else {
            let m = pre.next_of(a).unwrap();
            assert(pre.next_of(a).is_some());
            assert(pre.node_exists(a));
            assert(a != nw);
            Self::lemma_reaches_splice(pre, post, nd, nw, m, b, (f - 1) as nat);
            // recursion gives post.reaches(m, b, 2*(f-1)+2) == post.reaches(m, b, 2*f)
            if a == nd {
                assert(post.next_of(nd) == Some(nw));
                assert(post.next_of(nw) == Some(m));
                post.lemma_reaches_step(nw, m, b, (2 * f) as nat);
                post.lemma_reaches_step(nd, nw, b, (2 * f + 1) as nat);
            } else {
                assert(post.next_of(a) == Some(m));
                post.lemma_reaches_step(a, m, b, (2 * f) as nat);
                post.lemma_reaches_fuel_mono(a, b, (2 * f + 1) as nat, (2 * f + 2) as nat);
            }
        }
    }
}

// ===========================================================================
// The empty list satisfies chain validity (base case)
// ===========================================================================

impl<T> DoublyLinkedList<T> {
    // For a freshly created list (no slots at all) the property holds
    // vacuously: there are no live nodes and both endpoints are NULL.
    pub proof fn lemma_empty_valid(&self)
        requires
            self.data@.len() == 0,
            self.first == NULL,
            self.last == NULL,
        ensures self.valid_chain(),
    {
        // No id satisfies node_exists, so every forall is vacuous and both
        // endpoint clauses hold because first == last == NULL.
        assert forall|id: u32| #[trigger] self.node_exists(id) implies false by {
            assert(!(0 <= id < self.data@.len()));
        }
    }
}

// ===========================================================================
// Constructor
// ===========================================================================

impl<T> DoublyLinkedList<T> {
    // Mirrors `new`. Capacity is ignored at the spec level (it does not affect
    // the abstract list). Establishes the chain-validity property up front.
    pub fn new() -> (result: Self)
        ensures
            result.data@.len() == 0,
            result.first == NULL,
            result.last == NULL,
            result.valid_chain(),
    {
        let result = DoublyLinkedList {
            data: Vec::new(),
            free_list: Vec::new(),
            first: NULL,
            last: NULL,
        };
        proof {
            result.lemma_empty_valid();
        }
        result
    }
}

// ===========================================================================
// Read-only observations (fully verified against the implementation)
// ===========================================================================

impl<T> DoublyLinkedList<T> {
    // Mirrors `element`.
    fn element(&self, handle: u32) -> (result: Option<&Element<T>>)
        ensures
            result.is_some() == self.node_exists(handle),
            result.is_some() ==> *result.unwrap() == self.elem(handle),
    {
        let index = handle as usize;
        if index < self.data.len() {
            match &self.data[index] {
                Some(e) => Some(e),
                None => None,
            }
        } else {
            None
        }
    }

    // Mirrors `next`: Some(next) when the node exists and has a successor.
    fn next(&self, node: u32) -> (result: Option<u32>)
        ensures result == self.next_of(node),
    {
        let index = node as usize;
        if index < self.data.len() {
            match &self.data[index] {
                Some(e) => {
                    if e.next != NULL {
                        Some(e.next)
                    } else {
                        None
                    }
                }
                None => None,
            }
        } else {
            None
        }
    }

    // Mirrors `prec`.
    fn prec(&self, node: u32) -> (result: Option<u32>)
        ensures result == self.prec_of(node),
    {
        let index = node as usize;
        if index < self.data.len() {
            match &self.data[index] {
                Some(e) => {
                    if e.prec != NULL {
                        Some(e.prec)
                    } else {
                        None
                    }
                }
                None => None,
            }
        } else {
            None
        }
    }

    // Mirrors `first`.
    fn first(&self) -> (result: Option<u32>)
        ensures
            result.is_some() <==> self.first != NULL,
            result.is_some() ==> result.unwrap() == self.first,
    {
        if self.first != NULL {
            Some(self.first)
        } else {
            None
        }
    }

    // Mirrors `last`.
    fn last(&self) -> (result: Option<u32>)
        ensures
            result.is_some() <==> self.last != NULL,
            result.is_some() ==> result.unwrap() == self.last,
    {
        if self.last != NULL {
            Some(self.last)
        } else {
            None
        }
    }
}

// ===========================================================================
// Emptiness test (loop with invariant + decreases, fully verified)
// ===========================================================================

impl<T> DoublyLinkedList<T> {
    // Mirrors `is_empty`: true iff no slot is occupied.
    fn is_empty(&self) -> (result: bool)
        ensures
            result <==> (forall|i: int| 0 <= i < self.data@.len() ==> self.data@[i].is_none()),
    {
        let mut i: usize = 0;
        let n = self.data.len();
        while i < n
            invariant
                0 <= i <= n,
                n == self.data@.len(),
                forall|k: int| 0 <= k < i ==> self.data@[k].is_none(),
            decreases n - i,
        {
            if self.data[i].is_some() {
                assert(self.data@[i as int].is_some());
                return false;
            }
            i += 1;
        }
        true
    }
}

// ===========================================================================
// A correct single-node list satisfies chain validity
//
// This is the post-state the fixed `add_first_element` produces: the only live
// node (at any index, possibly amid freed holes) has NULL links and is both
// `first` and `last`. We prove it satisfies `valid_chain`.
// ===========================================================================

impl<T> DoublyLinkedList<T> {
    // A list whose ONLY live node is `node` (any index, possibly amid freed
    // holes) with NULL links and first == last == node is a
    // valid chain. This is the post-state of the fixed `add_first_element`.
    pub proof fn lemma_single_live_node_valid(&self, node: u32)
        requires
            self.data@.len() <= u32::MAX,
            self.node_exists(node),
            self.first == node,
            self.last == node,
            self.elem(node).next == NULL,
            self.elem(node).prec == NULL,
            forall|id: u32| #[trigger] self.node_exists(id) ==> id == node,
        ensures
            self.valid_chain(),
    {
        assert(node != NULL);
        assert(self.next_of(node).is_none());
        assert(self.prec_of(node).is_none());
        assert forall|id: u32| #[trigger] self.node_exists(id) implies
            self.reachable(self.first, id) && self.reachable(id, self.last) by {
            assert(id == node);
            self.lemma_reachable_self(node);
        }
    }

    // A live node forces `first` to be a real handle: with valid_chain, every
    // live node is reachable from `first`, and NULL reaches nothing live.
    pub proof fn lemma_nonempty_first(&self, w: u32)
        requires
            self.valid_chain(),
            self.data@.len() <= u32::MAX,
            self.node_exists(w),
        ensures
            self.first != NULL,
    {
        if self.first == NULL {
            assert(self.reachable(self.first, w));     // reachable_from_first(w)
            assert(w != NULL);
            assert(!self.node_exists(NULL));
            assert(self.next_of(NULL).is_none());
            assert forall|f: nat| !self.reaches(NULL, w, f) by {
            }
            assert(!self.reachable(NULL, w));
        }
    }
}

// ===========================================================================
// (BUG FIXED) The earlier `add_first_element` defect is gone: index_impl.rs now
// allocates a slot (recycling freed holes) instead of pushing at a hard-coded
// index 0. The previous verified counterexample lemma — which proved the buggy
// post-state `data = [None, Some(_)]`, first = last = 0 violated valid_chain —
// no longer corresponds to any reachable state, so it has been removed. Every
// operation below is now proven to PRESERVE valid_chain on all paths, including
// inserting into a list that was emptied by deletes.
// ===========================================================================

// ===========================================================================
// Value accessor (read-only, verified against the implementation)
// ===========================================================================

impl<T> DoublyLinkedList<T> {
    // Mirrors `value`.
    fn value(&self, node: u32) -> (result: Option<&T>)
        ensures
            result.is_some() == self.node_exists(node),
            result.is_some() ==> *result.unwrap() == self.elem(node).value,
    {
        let index = node as usize;
        if index < self.data.len() {
            match &self.data[index] {
                Some(e) => Some(&e.value),
                None => None,
            }
        } else {
            None
        }
    }
}

// ===========================================================================
// Internal helpers (verified against the implementation)
// ===========================================================================

impl<T> DoublyLinkedList<T> {
    // Mirrors `link`: sets n1.next = n2 and n2.prec = n1, each only if that node
    // is a real (in-range) slot. NULL endpoints are out of range, so a link to
    // NULL writes just the one side, exactly like the original `unwrap`-guarded
    // code. We require the touched slots to be live (the original would panic
    // otherwise) and forbid in-range aliasing (never happens at call sites).
    fn link(&mut self, n1: u32, n2: u32)
        requires
            (n1 as int) < old(self).data@.len() ==> old(self).data@[n1 as int].is_some(),
            (n2 as int) < old(self).data@.len() ==> old(self).data@[n2 as int].is_some(),
            (n1 == n2) ==> (n1 as int) >= old(self).data@.len(),
        ensures
            final(self).data@.len() == old(self).data@.len(),
            final(self).first == old(self).first,
            final(self).last == old(self).last,
            final(self).free_list@ == old(self).free_list@,
            (n1 as int) < old(self).data@.len() ==> {
                &&& final(self).data@[n1 as int].is_some()
                &&& final(self).data@[n1 as int]->Some_0.next == n2
                &&& final(self).data@[n1 as int]->Some_0.prec
                        == old(self).data@[n1 as int]->Some_0.prec
                &&& final(self).data@[n1 as int]->Some_0.value
                        == old(self).data@[n1 as int]->Some_0.value
            },
            (n2 as int) < old(self).data@.len() ==> {
                &&& final(self).data@[n2 as int].is_some()
                &&& final(self).data@[n2 as int]->Some_0.prec == n1
                &&& final(self).data@[n2 as int]->Some_0.next
                        == old(self).data@[n2 as int]->Some_0.next
                &&& final(self).data@[n2 as int]->Some_0.value
                        == old(self).data@[n2 as int]->Some_0.value
            },
            forall|k: int|
                0 <= k < old(self).data@.len() && k != n1 as int && k != n2 as int
                    ==> final(self).data@[k] == old(self).data@[k],
    {
        let idx1 = n1 as usize;
        let idx2 = n2 as usize;
        let count = self.data.len();
        if idx1 < count {
            self.data[idx1].as_mut().unwrap().next = n2;
        }
        if idx2 < count {
            self.data[idx2].as_mut().unwrap().prec = n1;
        }
    }

    // Mirrors `allocate`: reuse a free slot if any, else push a new slot. The
    // returned slot holds a fresh, unlinked node. Sound because `free_list_wf`
    // guarantees the reused index is a genuine hole.
    fn allocate(&mut self, value: T) -> (idx: u32)
        requires
            old(self).free_list_wf(),
            old(self).data@.len() < u32::MAX,
        ensures
            final(self).free_list_wf(),
            (idx as int) < final(self).data@.len(),
            old(self).data@.len() <= final(self).data@.len() <= old(self).data@.len() + 1,
            final(self).data@[idx as int].is_some(),
            final(self).data@[idx as int]->Some_0.next == NULL,
            final(self).data@[idx as int]->Some_0.prec == NULL,
            final(self).data@[idx as int]->Some_0.value == value,
            final(self).first == old(self).first,
            final(self).last == old(self).last,
            idx as int >= old(self).data@.len() || old(self).data@[idx as int].is_none(),
            // if the store grew, it grew by pushing exactly at the old end
            final(self).data@.len() == old(self).data@.len() + 1
                ==> (idx as int) == old(self).data@.len(),
            forall|k: int|
                0 <= k < old(self).data@.len() && k != idx as int
                    ==> final(self).data@[k] == old(self).data@[k],
    {
        let allocated = self.data.len();
        let popped = self.free_list.pop();
        let idx: usize = match popped {
            Some(f) => f as usize,
            None => allocated,
        };
        if idx < allocated {
            self.data.set(idx, Some(Element { next: NULL, prec: NULL, value }));
        } else {
            self.data.push(Some(Element { next: NULL, prec: NULL, value }));
        }
        proof {
            // pop() removed at most the last free index; the surviving prefix is
            // byte-for-byte the old free list, and `data` ops never touch it.
            assert(self.free_list@.len() <= old(self).free_list@.len());
            assert(forall|i: int|
                0 <= i < self.free_list@.len() ==> self.free_list@[i] == old(self).free_list@[i]);

            // First conjunct of free_list_wf: every surviving free index still
            // points at an in-range hole.
            assert forall|i: int| 0 <= i < self.free_list@.len() implies
                0 <= #[trigger] self.free_list@[i] < self.data@.len()
                    && self.data@[self.free_list@[i] as int].is_none()
            by {
                assert(self.free_list@[i] == old(self).free_list@[i]);
                assert(0 <= old(self).free_list@[i] < old(self).data@.len());
                if idx < allocated {
                    // reuse path: idx is the popped (old last) index; distinctness
                    // keeps every surviving index away from the slot we filled.
                    assert(idx as u32 == old(self).free_list@[old(self).free_list@.len() - 1]);
                    assert(i != old(self).free_list@.len() - 1);
                    assert(old(self).free_list@[i]
                        != old(self).free_list@[old(self).free_list@.len() - 1]);
                }
                // push path: idx >= old len > every old free index, so untouched.
            }

            // Second conjunct: distinctness is inherited from the prefix.
            assert forall|i: int, j: int|
                0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() && i != j
                implies self.free_list@[i] != self.free_list@[j]
            by {
                assert(self.free_list@[i] == old(self).free_list@[i]);
                assert(self.free_list@[j] == old(self).free_list@[j]);
            }
        }
        idx as u32
    }

    // Mirrors `add_first_element`: only sound when the backing store is truly
    // empty (the original comment says "assume self.data is empty"). Under that
    // precondition it builds a valid single-node chain.
    // FIXED: allocate a slot (reusing a freed hole if any) instead of pushing at
    // a hard-coded index 0. Sound whenever the list is logically empty — even if
    // the backing Vec still holds tombstones from earlier deletes.
    fn add_first_element(&mut self, value: T) -> (idx: u32)
        requires
            old(self).free_list_wf(),
            old(self).data@.len() < u32::MAX,
            old(self).first == NULL,
            old(self).last == NULL,
            forall|i: int| 0 <= i < old(self).data@.len() ==> old(self).data@[i].is_none(),
        ensures
            final(self).free_list_wf(),
            final(self).node_exists(idx),
            final(self).elem(idx).value == value,
            final(self).next_of(idx).is_none(),
            final(self).prec_of(idx).is_none(),
            final(self).first == idx,
            final(self).last == idx,
            final(self).valid_chain(),
            forall|id: u32| old(self).node_exists(id) ==> #[trigger] final(self).node_exists(id),
    {
        let node = self.allocate(value);
        self.first = node;
        self.last = node;
        proof {
            let s0 = old(self);
            assert(self.node_exists(node));
            assert(self.elem(node).next == NULL);
            assert(self.elem(node).prec == NULL);
            // `node` is the only live node: every old slot was None and allocate
            // touched only `node`.
            assert forall|id: u32| #[trigger] self.node_exists(id) implies id == node by {
                if id != node {
                    if (id as int) < s0.data@.len() {
                        assert(self.data@[id as int] == s0.data@[id as int]);
                        assert(s0.data@[id as int].is_none());
                    } else {
                        assert(self.data@.len() <= s0.data@.len() + 1);
                        assert(self.data@.len() == s0.data@.len() + 1
                            ==> node as int == s0.data@.len());
                    }
                }
            }
            self.lemma_single_live_node_valid(node);
        }
        node
    }
}

// ===========================================================================
// push_back — proven to PRESERVE reachability-based chain validity (ALL paths)
//
// With the fixed `add_first_element`, both branches are correct: the empty path
// builds a valid single-node list (reusing a freed slot), the non-empty path
// appends after the old tail. No bug-masking precondition is needed anymore.
// ===========================================================================

impl<T> DoublyLinkedList<T> {
    fn push_back(&mut self, value: T) -> (node: u32)
        requires
            old(self).wf(),
            old(self).data@.len() < u32::MAX,
        ensures
            final(self).wf(),
            final(self).node_exists(node),
            final(self).last == node,
            final(self).next_of(node).is_none(),
            final(self).elem(node).value == value,
            old(self).last == NULL ==> final(self).prec_of(node).is_none(),
            old(self).last != NULL ==> final(self).prec_of(node) == Some(old(self).last),
            old(self).first != NULL ==> final(self).first == old(self).first,
            forall|id: u32| old(self).node_exists(id) ==> #[trigger] final(self).node_exists(id),
    {
        let empty = self.is_empty();
        if empty {
            proof {
                // is_empty() + wf  ==>  first == NULL == last and every slot None:
                // exactly add_first_element's precondition.
                assert(forall|i: int| 0 <= i < self.data@.len() ==> self.data@[i].is_none());
                if self.first != NULL {
                    assert(self.node_exists(self.first));
                }
                if self.last != NULL {
                    assert(self.node_exists(self.last));
                }
            }
            let node = self.add_first_element(value);
            node
        } else {
            proof {
                // is_empty() == false  ==>  some live node  ==>  first/last != NULL.
                assert(!(forall|i: int|
                    0 <= i < self.data@.len() ==> self.data@[i].is_none()));
                let w = choose|i: int|
                    0 <= i < self.data@.len() && self.data@[i].is_some();
                assert(self.node_exists(w as u32));
                self.lemma_nonempty_first(w as u32);
                assert(self.first != NULL);
                assert(self.last != NULL);
            }
            let ol = self.last;
            proof {
                assert(self.node_exists(ol));      // last is live (wf + last != NULL)
            }
            let node = self.allocate(value);
            let ghost d1 = self.data@;            // store right after allocate
            proof {
                assert(node != ol);                // fresh slot vs. live old tail
                assert(self.node_exists(ol));      // preserved through allocate
            }
            self.link(ol, node);
            let ghost d2 = self.data@;            // store right after link
            self.last = node;
            proof {
                let s0 = old(self);
                assert(node != NULL);
                assert(self.node_exists(node));
                assert(self.elem(node).value == value);
                assert(self.elem(node).next == NULL);
                assert(self.next_of(node).is_none());
                assert(self.elem(node).prec == ol);
                assert(self.next_of(ol) == Some(node));
                assert(self.last == node);
                assert(self.first == s0.first);
                assert(!s0.node_exists(node));
                assert(s0.node_exists(ol));
                assert(s0.next_of(ol).is_none());
                // F3: `ol`'s predecessor field is untouched (we only set its next).
                assert(self.elem(ol).prec == s0.elem(ol).prec);
                // length: the only index beyond s0's range that can be live is `node`.
                assert(self.data@.len() == s0.data@.len()
                    || (self.data@.len() == s0.data@.len() + 1 && node as int == s0.data@.len()));

                // Combined frame: every slot other than `ol`/`node` is byte-for-byte
                // what it was in s0 (chained through the two intermediate stores).
                assert forall|k: int|
                    0 <= k < s0.data@.len() && k != node as int && k != ol as int
                    implies #[trigger] self.data@[k] == s0.data@[k] by {
                    assert(d1[k] == s0.data@[k]);   // allocate frame
                    assert(d2[k] == d1[k]);          // link frame
                }

                // F1: existence agrees with s0 for every node except the fresh one.
                assert forall|id: u32| id != node implies
                    (#[trigger] self.node_exists(id)) <==> s0.node_exists(id) by {
                    if id == ol {
                        assert(self.node_exists(ol) && s0.node_exists(ol));
                    } else if (id as int) < s0.data@.len() {
                        assert(self.data@[id as int] == s0.data@[id as int]);
                    } else {
                        assert(!s0.node_exists(id));
                        assert(!self.node_exists(id));
                    }
                }
                // F2: slots are identical to s0 except at `ol` and `node`.
                assert forall|id: u32| id != node && id != ol && s0.node_exists(id) implies
                    #[trigger] self.data@[id as int] == s0.data@[id as int] by {
                }

                // Old live nodes survive (special case of F1).
                assert forall|id: u32| s0.node_exists(id) implies #[trigger] self.node_exists(id) by {
                    assert(id != node);
                }

                // next_of agreement: pre and post differ only at `ol`, which had
                // no successor in pre.
                assert forall|id: u32| #[trigger] s0.next_of(id) == self.next_of(id) || id == ol by {
                    if id != ol && id != node {
                        if s0.node_exists(id) {
                            assert(self.data@[id as int] == s0.data@[id as int]);
                        } else {
                            assert(!self.node_exists(id));
                        }
                    } else if id == node {
                        assert(!s0.node_exists(node));
                        assert(self.next_of(node).is_none());
                    }
                }

                // free_list_wf carried by allocate + link (free indices are holes,
                // distinct from the live nodes ol/node we touched).
                assert(self.free_list_wf());

                // endpoints_wf.
                assert(self.endpoints_wf());

                // links_consistent.
                assert forall|id: u32| #[trigger] self.node_exists(id) implies {
                    &&& (self.next_of(id).is_some() ==> self.node_exists(self.next_of(id).unwrap()))
                    &&& (self.prec_of(id).is_some() ==> self.node_exists(self.prec_of(id).unwrap()))
                    &&& (self.next_of(id).is_some() ==> self.prec_of(self.next_of(id).unwrap()) == Some(id))
                    &&& (self.prec_of(id).is_some() ==> self.next_of(self.prec_of(id).unwrap()) == Some(id))
                } by {
                    if id == node {
                    } else if id == ol {
                    } else {
                        assert(self.data@[id as int] == s0.data@[id as int]);
                    }
                }

                // reachable_from_first: old nodes via frame, new node via append.
                assert forall|id: u32| #[trigger] self.node_exists(id)
                    implies self.reachable(self.first, id) by {
                    if id == node {
                        assert(s0.reachable(s0.first, ol));
                        let f = choose|f: nat| s0.reaches(s0.first, ol, f);
                        Self::lemma_frame_noext(s0, self, ol, s0.first, ol, f);
                        self.lemma_reaches_append(s0.first, ol, node, f);
                        assert(self.reaches(self.first, node, f + 1));
                    } else {
                        assert(s0.node_exists(id));
                        assert(s0.reachable(s0.first, id));
                        let f = choose|f: nat| s0.reaches(s0.first, id, f);
                        Self::lemma_frame_noext(s0, self, ol, s0.first, id, f);
                        assert(self.reaches(self.first, id, f));
                    }
                }

                // reaches_last (== node): old nodes reach ol then step to node.
                assert forall|id: u32| #[trigger] self.node_exists(id)
                    implies self.reachable(id, self.last) by {
                    if id == node {
                        assert(self.reaches(node, node, 0));
                    } else {
                        assert(s0.node_exists(id));
                        assert(s0.reachable(id, s0.last));
                        let f = choose|f: nat| s0.reaches(id, s0.last, f);
                        Self::lemma_frame_noext(s0, self, ol, id, ol, f);
                        self.lemma_reaches_append(id, ol, node, f);
                        assert(self.reaches(id, node, f + 1));
                    }
                }

                assert(self.valid_chain());
            }
            node
        }
    }
}

// ===========================================================================
// push_front — proven to PRESERVE reachability-based chain validity (ALL paths)
//
// Symmetric to push_back. With the fixed add_first_element the empty path is
// also correct (a valid single-node list), so no bug-masking precondition.
// ===========================================================================

impl<T> DoublyLinkedList<T> {
    fn push_front(&mut self, value: T) -> (node: u32)
        requires
            old(self).wf(),
            old(self).data@.len() < u32::MAX,
        ensures
            final(self).wf(),
            final(self).node_exists(node),
            final(self).first == node,
            final(self).prec_of(node).is_none(),
            final(self).elem(node).value == value,
            old(self).first == NULL ==> final(self).next_of(node).is_none(),
            old(self).first != NULL ==> final(self).next_of(node) == Some(old(self).first),
            old(self).last != NULL ==> final(self).last == old(self).last,
            forall|id: u32| old(self).node_exists(id) ==> #[trigger] final(self).node_exists(id),
    {
        let empty = self.is_empty();
        if empty {
            proof {
                assert(forall|i: int| 0 <= i < self.data@.len() ==> self.data@[i].is_none());
                if self.first != NULL {
                    assert(self.node_exists(self.first));
                }
                if self.last != NULL {
                    assert(self.node_exists(self.last));
                }
            }
            let node = self.add_first_element(value);
            node
        } else {
            proof {
                assert(!(forall|i: int|
                    0 <= i < self.data@.len() ==> self.data@[i].is_none()));
                let w = choose|i: int|
                    0 <= i < self.data@.len() && self.data@[i].is_some();
                assert(self.node_exists(w as u32));
                self.lemma_nonempty_first(w as u32);
                assert(self.first != NULL);
                assert(self.last != NULL);
            }
            let of = self.first;
            proof {
                assert(self.node_exists(of));
            }
            let node = self.allocate(value);
            let ghost d1 = self.data@;
            proof {
                assert(node != of);
                assert(self.node_exists(of));
            }
            self.link(node, of);
            let ghost d2 = self.data@;
            self.first = node;
            proof {
                let s0 = old(self);
                assert(node != NULL);
                assert(self.node_exists(node));
                assert(self.elem(node).value == value);
                assert(self.elem(node).prec == NULL);
                assert(self.prec_of(node).is_none());
                assert(self.elem(node).next == of);
                assert(self.next_of(node) == Some(of));
                assert(self.first == node);
                assert(self.last == s0.last);
                assert(!s0.node_exists(node));
                assert(s0.node_exists(of));
                assert(s0.prec_of(of).is_none());
                // of's `next` is untouched (we only set its prec).
                assert(self.elem(of).next == s0.elem(of).next);
                assert(self.data@.len() == s0.data@.len()
                    || (self.data@.len() == s0.data@.len() + 1 && node as int == s0.data@.len()));

                // Combined frame: every slot other than `of`/`node` equals s0.
                assert forall|k: int|
                    0 <= k < s0.data@.len() && k != node as int && k != of as int
                    implies #[trigger] self.data@[k] == s0.data@[k] by {
                    assert(d1[k] == s0.data@[k]);
                    assert(d2[k] == d1[k]);
                }

                // F1: existence agreement (away from the fresh node).
                assert forall|id: u32| id != node implies
                    (#[trigger] self.node_exists(id)) <==> s0.node_exists(id) by {
                    if id == of {
                        assert(self.node_exists(of) && s0.node_exists(of));
                    } else if (id as int) < s0.data@.len() {
                        assert(self.data@[id as int] == s0.data@[id as int]);
                    } else {
                        assert(!s0.node_exists(id));
                        assert(!self.node_exists(id));
                    }
                }
                // F2: slot equality away from `of`/`node`.
                assert forall|id: u32| id != node && id != of && s0.node_exists(id) implies
                    #[trigger] self.data@[id as int] == s0.data@[id as int] by {
                }

                // Old live nodes survive.
                assert forall|id: u32| s0.node_exists(id) implies #[trigger] self.node_exists(id) by {
                    assert(id != node);
                }

                // next_of agreement: only the fresh node gained a successor; every
                // pre-existing next-link is unchanged.
                assert forall|id: u32| #[trigger] s0.next_of(id) == self.next_of(id) || id == node by {
                    if id != node {
                        if s0.node_exists(id) {
                            if id == of {
                                assert(self.elem(of).next == s0.elem(of).next);
                            } else {
                                assert(self.data@[id as int] == s0.data@[id as int]);
                            }
                        } else {
                            assert(!self.node_exists(id));
                        }
                    }
                }
                assert(s0.next_of(node).is_none());

                assert(self.free_list_wf());
                assert(self.endpoints_wf());

                // links_consistent.
                assert forall|id: u32| #[trigger] self.node_exists(id) implies {
                    &&& (self.next_of(id).is_some() ==> self.node_exists(self.next_of(id).unwrap()))
                    &&& (self.prec_of(id).is_some() ==> self.node_exists(self.prec_of(id).unwrap()))
                    &&& (self.next_of(id).is_some() ==> self.prec_of(self.next_of(id).unwrap()) == Some(id))
                    &&& (self.prec_of(id).is_some() ==> self.next_of(self.prec_of(id).unwrap()) == Some(id))
                } by {
                    if id == node {
                    } else if id == of {
                    } else {
                        assert(self.data@[id as int] == s0.data@[id as int]);
                    }
                }

                // reachable_from_first (first == node): node trivially; old nodes
                // are reached by stepping node -> old_first -> ... (front-extend).
                assert forall|id: u32| #[trigger] self.node_exists(id)
                    implies self.reachable(self.first, id) by {
                    if id == node {
                        assert(self.reaches(node, node, 0));
                    } else {
                        assert(s0.node_exists(id));
                        assert(s0.reachable(s0.first, id));
                        let f = choose|f: nat| s0.reaches(s0.first, id, f);
                        Self::lemma_frame_noext(s0, self, node, of, id, f);
                        self.lemma_reaches_step(node, of, id, f);
                        assert(self.reaches(self.first, id, f + 1));
                    }
                }

                // reaches_last (== old last): old nodes via frame; node via one
                // step to old_first then the old path to last.
                assert forall|id: u32| #[trigger] self.node_exists(id)
                    implies self.reachable(id, self.last) by {
                    if id == node {
                        assert(s0.reachable(s0.first, s0.last));
                        let f = choose|f: nat| s0.reaches(s0.first, s0.last, f);
                        Self::lemma_frame_noext(s0, self, node, of, s0.last, f);
                        self.lemma_reaches_step(node, of, s0.last, f);
                        assert(self.reaches(node, self.last, f + 1));
                    } else {
                        assert(s0.node_exists(id));
                        assert(s0.reachable(id, s0.last));
                        let f = choose|f: nat| s0.reaches(id, s0.last, f);
                        Self::lemma_frame_noext(s0, self, node, id, s0.last, f);
                        assert(self.reaches(id, self.last, f));
                    }
                }

                assert(self.valid_chain());
            }
            node
        }
    }
}


// ===========================================================================
// Chain-preservation engine for mid-list splices (insert_after / insert_before)
// ===========================================================================

impl<T> DoublyLinkedList<T> {
    // A node whose successor is None can only reach itself.
    pub proof fn lemma_reaches_dead_end(&self, a: u32, b: u32, f: nat)
        requires
            self.reaches(a, b, f),
            self.next_of(a).is_none(),
        ensures
            a == b,
    {
    }

    // Inserting fresh `nw` after live `nd` preserves the whole chain.
    // `cn` is nd's old successor field (NULL if nd was the tail).
    #[verifier::rlimit(60)]
    pub proof fn lemma_splice_preserves(
        pre: &DoublyLinkedList<T>,
        post: &DoublyLinkedList<T>,
        nd: u32,
        nw: u32,
        cn: u32,
    )
        requires
            pre.valid_chain(),
            pre.data@.len() <= u32::MAX,
            pre.node_exists(nd),
            !pre.node_exists(nw),
            nw != NULL,
            post.node_exists(nw),
            cn == pre.elem(nd).next,
            post.first == pre.first,
            post.last == (if nd == pre.last { nw } else { pre.last }),
            forall|id: u32| id != nw ==> ((#[trigger] post.node_exists(id)) <==> pre.node_exists(id)),
            post.next_of(nd) == Some(nw),
            post.next_of(nw) == pre.next_of(nd),
            forall|id: u32| id != nd && id != nw ==> #[trigger] post.next_of(id) == pre.next_of(id),
            post.prec_of(nw) == Some(nd),
            post.prec_of(nd) == pre.prec_of(nd),
            cn != NULL ==> post.prec_of(cn) == Some(nw),
            forall|id: u32| id != nw && id != cn ==> #[trigger] post.prec_of(id) == pre.prec_of(id),
        ensures
            post.valid_chain(),
    {
        // Basic non-aliasing facts.
        assert(nd != nw);
        assert(pre.first != NULL);          // nd live => pre non-empty
        pre.lemma_no_self_loop(nd);
        assert(pre.next_of(nd) != Some(nd));
        let cn_real = cn != NULL;
        if cn_real {
            assert(pre.next_of(nd) == Some(cn));
            assert(pre.node_exists(cn));     // links_consistent
            assert(cn != nd);
            assert(cn != nw);
        }

        // endpoints_wf(post).
        assert(post.node_exists(pre.first));
        assert(pre.first != cn) by {
            if cn_real && pre.first == cn {
                assert(pre.prec_of(cn) == Some(nd));   // links_consistent
            }
        }
        assert(post.endpoints_wf()) by {
            if nd == pre.last {
                assert(pre.next_of(nd).is_none());     // pre endpoints: last has no next
                assert(cn == NULL);
                assert(post.next_of(nw).is_none());
            } else {
                assert(post.last == pre.last);
                assert(pre.last != nd);
                assert(pre.last != nw);
            }
        }

        // links_consistent(post).
        assert forall|id: u32| #[trigger] post.node_exists(id) implies {
            &&& (post.next_of(id).is_some() ==> post.node_exists(post.next_of(id).unwrap()))
            &&& (post.prec_of(id).is_some() ==> post.node_exists(post.prec_of(id).unwrap()))
            &&& (post.next_of(id).is_some() ==> post.prec_of(post.next_of(id).unwrap()) == Some(id))
            &&& (post.prec_of(id).is_some() ==> post.next_of(post.prec_of(id).unwrap()) == Some(id))
        } by {
            assert(pre.node_exists(id) || id == nw);
            if id == nd {
            } else if id == nw {
            } else if cn_real && id == cn {
            } else {
                // unchanged node: its neighbours are unchanged too
                assert(post.next_of(id) == pre.next_of(id));
                assert(post.prec_of(id) == pre.prec_of(id));
            }
        }

        // reachable_from_first(post).
        assert forall|id: u32| #[trigger] post.node_exists(id)
            implies post.reachable(post.first, id) by {
            if id == nw {
                assert(pre.reachable(pre.first, nd));
                let f = choose|f: nat| pre.reaches(pre.first, nd, f);
                Self::lemma_reaches_splice(pre, post, nd, nw, pre.first, nd, f);
                post.lemma_reaches_append(pre.first, nd, nw, (2 * f + 2) as nat);
            } else {
                assert(pre.node_exists(id));
                assert(pre.reachable(pre.first, id));
                let f = choose|f: nat| pre.reaches(pre.first, id, f);
                Self::lemma_reaches_splice(pre, post, nd, nw, pre.first, id, f);
            }
        }

        // reaches_last(post).
        assert forall|id: u32| #[trigger] post.node_exists(id)
            implies post.reachable(id, post.last) by {
            if nd == pre.last {
                if id == nw {
                    assert(post.reaches(nw, nw, 0));
                } else {
                    assert(pre.node_exists(id));
                    assert(pre.reachable(id, pre.last));
                    let f = choose|f: nat| pre.reaches(id, pre.last, f);
                    Self::lemma_reaches_splice(pre, post, nd, nw, id, pre.last, f);
                    post.lemma_reaches_append(id, nd, nw, (2 * f + 2) as nat);
                }
            } else {
                // nd is not the tail, so it has a real successor cn.
                assert(pre.reachable(nd, pre.last));
                if pre.next_of(nd).is_none() {
                    let ff = choose|ff: nat| pre.reaches(nd, pre.last, ff);
                    pre.lemma_reaches_dead_end(nd, pre.last, ff);
                }
                assert(cn_real);
                if id == nw {
                    assert(pre.reachable(cn, pre.last));
                    let g = choose|g: nat| pre.reaches(cn, pre.last, g);
                    Self::lemma_reaches_splice(pre, post, nd, nw, cn, pre.last, g);
                    post.lemma_reaches_step(nw, cn, pre.last, (2 * g + 2) as nat);
                } else {
                    assert(pre.node_exists(id));
                    assert(pre.reachable(id, pre.last));
                    let f = choose|f: nat| pre.reaches(id, pre.last, f);
                    Self::lemma_reaches_splice(pre, post, nd, nw, id, pre.last, f);
                }
            }
        }

        assert(post.valid_chain());
    }

    // Inserting fresh `nw` as the new head (before old head `of`) preserves the
    // chain. Used by insert_before when the target is the current head.
    #[verifier::rlimit(60)]
    pub proof fn lemma_prepend_preserves(
        pre: &DoublyLinkedList<T>,
        post: &DoublyLinkedList<T>,
        of: u32,
        nw: u32,
    )
        requires
            pre.valid_chain(),
            pre.data@.len() <= u32::MAX,
            pre.node_exists(of),
            of == pre.first,
            !pre.node_exists(nw),
            nw != NULL,
            post.node_exists(nw),
            post.first == nw,
            post.last == pre.last,
            forall|id: u32| id != nw ==> ((#[trigger] post.node_exists(id)) <==> pre.node_exists(id)),
            post.next_of(nw) == Some(of),
            post.prec_of(nw).is_none(),
            forall|id: u32| id != nw ==> #[trigger] post.next_of(id) == pre.next_of(id),
            post.prec_of(of) == Some(nw),
            forall|id: u32| id != nw && id != of ==> #[trigger] post.prec_of(id) == pre.prec_of(id),
        ensures
            post.valid_chain(),
    {
        assert(of != nw);
        assert(pre.first != NULL);
        assert(post.node_exists(of));

        // next-link agreement (only nw gained a successor).
        assert forall|id: u32| #[trigger] pre.next_of(id) == post.next_of(id) || id == nw by {
        }
        assert(pre.next_of(nw).is_none());

        assert(post.endpoints_wf());

        assert forall|id: u32| #[trigger] post.node_exists(id) implies {
            &&& (post.next_of(id).is_some() ==> post.node_exists(post.next_of(id).unwrap()))
            &&& (post.prec_of(id).is_some() ==> post.node_exists(post.prec_of(id).unwrap()))
            &&& (post.next_of(id).is_some() ==> post.prec_of(post.next_of(id).unwrap()) == Some(id))
            &&& (post.prec_of(id).is_some() ==> post.next_of(post.prec_of(id).unwrap()) == Some(id))
        } by {
            if id == nw {
            } else if id == of {
            } else {
                assert(post.next_of(id) == pre.next_of(id));
                assert(post.prec_of(id) == pre.prec_of(id));
            }
        }

        // reachable_from_first (first == nw): nw -> of -> ...
        assert forall|id: u32| #[trigger] post.node_exists(id)
            implies post.reachable(post.first, id) by {
            if id == nw {
                assert(post.reaches(nw, nw, 0));
            } else {
                assert(pre.node_exists(id));
                assert(pre.reachable(pre.first, id));
                let f = choose|f: nat| pre.reaches(pre.first, id, f);
                Self::lemma_frame_noext(pre, post, nw, of, id, f);
                post.lemma_reaches_step(nw, of, id, f);
            }
        }

        // reaches_last (== pre.last).
        assert forall|id: u32| #[trigger] post.node_exists(id)
            implies post.reachable(id, post.last) by {
            if id == nw {
                assert(pre.reachable(pre.first, pre.last));
                let f = choose|f: nat| pre.reaches(pre.first, pre.last, f);
                Self::lemma_frame_noext(pre, post, nw, of, pre.last, f);
                post.lemma_reaches_step(nw, of, pre.last, f);
            } else {
                assert(pre.node_exists(id));
                assert(pre.reachable(id, pre.last));
                let f = choose|f: nat| pre.reaches(id, pre.last, f);
                Self::lemma_frame_noext(pre, post, nw, id, pre.last, f);
            }
        }

        assert(post.valid_chain());
    }

    // Any node reached from a different node has a predecessor (the last hop in).
    pub proof fn lemma_no_pred_path(&self, src: u32, dst: u32, f: nat)
        requires
            self.valid_chain(),
            self.reaches(src, dst, f),
            src != dst,
        ensures
            self.prec_of(dst).is_some(),
        decreases f,
    {
        assert(self.next_of(src).is_some());
        let m = self.next_of(src).unwrap();
        if m == dst {
            assert(self.node_exists(src));
            assert(self.prec_of(dst) == Some(src));   // links_consistent
        } else {
            assert(self.reaches(m, dst, (f - 1) as nat));
            self.lemma_no_pred_path(m, dst, (f - 1) as nat);
        }
    }

    // A live node with no predecessor must be the head.
    pub proof fn lemma_prec_none_first(&self, id: u32)
        requires
            self.valid_chain(),
            self.data@.len() <= u32::MAX,
            self.node_exists(id),
            self.prec_of(id).is_none(),
        ensures
            id == self.first,
    {
        if id != self.first {
            assert(self.reachable(self.first, id));
            let f = choose|f: nat| self.reaches(self.first, id, f);
            self.lemma_no_pred_path(self.first, id, f);
        }
    }
}

// ===========================================================================
// insert_after / insert_before — verified BEHAVIOR (against the implementation)
//
// These splice a fresh node next to a given live node. We prove the full link
// behavior mandated by the abstract spec (new node's neighbors, the target's
// updated link, head/tail updates) and that the free list stays well-formed.
// (Reachability-chain preservation for mid-list splices is the heavier proof
// carried for push_back/push_front; see the report.)
// ===========================================================================

impl<T> DoublyLinkedList<T> {
    fn insert_after(&mut self, node: u32, value: T) -> (new_node: u32)
        requires
            old(self).wf(),
            old(self).node_exists(node),
            old(self).data@.len() < u32::MAX,
        ensures
            final(self).wf(),
            final(self).node_exists(new_node),
            final(self).elem(new_node).value == value,
            final(self).prec_of(new_node) == Some(node),
            final(self).next_of(node) == Some(new_node),
            final(self).next_of(new_node) == old(self).next_of(node),
            final(self).first == old(self).first,
            node == old(self).last ==> final(self).last == new_node,
            node != old(self).last ==> final(self).last == old(self).last,
            forall|id: u32| old(self).node_exists(id) ==> #[trigger] final(self).node_exists(id),
    {
        let empty = self.is_empty();
        if empty {
            proof {
                assert(self.node_exists(node));
                assert(self.data@[node as int].is_none());
                assert(false);
            }
            self.add_first_element(value)
        } else {
            proof {
                assert(node != NULL);
                old(self).lemma_no_self_loop(node);
            }
            let new_node = self.allocate(value);
            let ghost d1 = self.data@;
            let cnode_next = self.data[node as usize].as_ref().unwrap().next;
            proof {
                assert(cnode_next == old(self).elem(node).next);
                assert(node != new_node);
                assert(cnode_next != node);
                if cnode_next != NULL {
                    assert(old(self).node_exists(cnode_next));   // links_consistent
                    assert(self.node_exists(cnode_next));        // preserved by allocate
                    assert(new_node != cnode_next);
                }
            }
            self.link(node, new_node);
            let ghost d2 = self.data@;
            proof {
                if cnode_next != NULL {
                    assert(self.node_exists(cnode_next));        // preserved by link
                }
            }
            self.link(new_node, cnode_next);
            let ghost d3 = self.data@;
            if node == self.last {
                self.last = new_node;
            }
            proof {
                let s0 = old(self);
                assert(new_node != NULL);

                // Behavioral link facts.
                assert(self.node_exists(node));
                assert(self.elem(node).next == new_node);
                assert(self.elem(node).prec == s0.elem(node).prec);     // node's prec untouched
                assert(self.next_of(node) == Some(new_node));
                assert(self.elem(new_node).prec == node);
                assert(self.prec_of(new_node) == Some(node));
                assert(self.next_of(new_node) == s0.next_of(node));
                if cnode_next != NULL {
                    assert(self.elem(cnode_next).prec == new_node);
                    assert(self.elem(cnode_next).next == s0.elem(cnode_next).next);
                    assert(self.prec_of(cnode_next) == Some(new_node));
                }
                assert(self.data@.len() == s0.data@.len()
                    || (self.data@.len() == s0.data@.len() + 1 && new_node as int == s0.data@.len()));

                // Combined slot frame (away from node / new_node / cnode_next).
                assert forall|k: int|
                    0 <= k < s0.data@.len() && k != node as int && k != new_node as int
                        && k != cnode_next as int
                    implies #[trigger] self.data@[k] == s0.data@[k] by {
                    assert(d1[k] == s0.data@[k]);
                    assert(d2[k] == d1[k]);
                    assert(d3[k] == d2[k]);
                }

                // Existence / next / prec frames feeding lemma_splice_preserves.
                assert forall|id: u32| id != new_node implies
                    (#[trigger] self.node_exists(id)) <==> s0.node_exists(id) by {
                    if id == node {
                    } else if cnode_next != NULL && id == cnode_next {
                    } else if (id as int) < s0.data@.len() {
                        assert(self.data@[id as int] == s0.data@[id as int]);
                    } else {
                        assert(!s0.node_exists(id));
                        assert(!self.node_exists(id));
                    }
                }
                assert forall|id: u32| id != node && id != new_node implies
                    #[trigger] self.next_of(id) == s0.next_of(id) by {
                    if cnode_next != NULL && id == cnode_next {
                    } else if (id as int) < s0.data@.len() {
                        assert(self.data@[id as int] == s0.data@[id as int]);
                    } else {
                        assert(!s0.node_exists(id));
                        assert(!self.node_exists(id));
                    }
                }
                assert forall|id: u32| id != new_node && id != cnode_next implies
                    #[trigger] self.prec_of(id) == s0.prec_of(id) by {
                    if id == node {
                    } else if (id as int) < s0.data@.len() {
                        assert(self.data@[id as int] == s0.data@[id as int]);
                    } else {
                        assert(!s0.node_exists(id));
                        assert(!self.node_exists(id));
                    }
                }

                Self::lemma_splice_preserves(s0, self, node, new_node, cnode_next);
                assert(self.valid_chain());
                assert(self.free_list_wf());

                assert forall|id: u32| s0.node_exists(id) implies #[trigger] self.node_exists(id) by {
                    assert(id != new_node);
                }
            }
            new_node
        }
    }

    fn insert_before(&mut self, node: u32, value: T) -> (new_node: u32)
        requires
            old(self).wf(),
            old(self).node_exists(node),
            old(self).data@.len() < u32::MAX,
        ensures
            final(self).wf(),
            final(self).node_exists(new_node),
            final(self).elem(new_node).value == value,
            final(self).next_of(new_node) == Some(node),
            final(self).prec_of(node) == Some(new_node),
            final(self).prec_of(new_node) == old(self).prec_of(node),
            final(self).last == old(self).last,
            node == old(self).first ==> final(self).first == new_node,
            node != old(self).first ==> final(self).first == old(self).first,
            forall|id: u32| old(self).node_exists(id) ==> #[trigger] final(self).node_exists(id),
    {
        let empty = self.is_empty();
        if empty {
            proof {
                assert(self.node_exists(node));
                assert(self.data@[node as int].is_none());
                assert(false);
            }
            self.add_first_element(value)
        } else {
            proof {
                assert(node != NULL);
                old(self).lemma_no_self_loop(node);
            }
            let new_node = self.allocate(value);
            let ghost d1 = self.data@;
            let cnode_prec = self.data[node as usize].as_ref().unwrap().prec;
            proof {
                assert(cnode_prec == old(self).elem(node).prec);
                assert(node != new_node);
                assert(cnode_prec != node);
                if cnode_prec != NULL {
                    assert(old(self).node_exists(cnode_prec));   // links_consistent
                    assert(self.node_exists(cnode_prec));        // preserved by allocate
                    assert(new_node != cnode_prec);
                }
            }
            self.link(new_node, node);
            let ghost d2 = self.data@;
            proof {
                if cnode_prec != NULL {
                    assert(self.node_exists(cnode_prec));        // preserved by link
                }
            }
            self.link(cnode_prec, new_node);
            let ghost d3 = self.data@;
            if node == self.first {
                self.first = new_node;
            }
            proof {
                let s0 = old(self);
                assert(new_node != NULL);

                // shared field-level facts
                assert(self.node_exists(node));
                assert(self.elem(node).next == s0.elem(node).next);   // node's next untouched
                assert(self.elem(node).prec == new_node);
                assert(self.elem(new_node).next == node);
                assert(self.elem(new_node).prec == cnode_prec);
                assert(self.next_of(new_node) == Some(node));
                assert(self.prec_of(node) == Some(new_node));
                assert(self.prec_of(new_node) == s0.prec_of(node));
                if cnode_prec != NULL {
                    assert(self.elem(cnode_prec).next == new_node);
                    assert(self.elem(cnode_prec).prec == s0.elem(cnode_prec).prec);
                }
                assert(self.data@.len() == s0.data@.len()
                    || (self.data@.len() == s0.data@.len() + 1 && new_node as int == s0.data@.len()));

                // combined slot frame (away from node / new_node / cnode_prec)
                assert forall|k: int|
                    0 <= k < s0.data@.len() && k != node as int && k != new_node as int
                        && k != cnode_prec as int
                    implies #[trigger] self.data@[k] == s0.data@[k] by {
                    assert(d1[k] == s0.data@[k]);
                    assert(d2[k] == d1[k]);
                    assert(d3[k] == d2[k]);
                }

                // existence frame (shared)
                assert forall|id: u32| id != new_node implies
                    (#[trigger] self.node_exists(id)) <==> s0.node_exists(id) by {
                    if id == node {
                    } else if cnode_prec != NULL && id == cnode_prec {
                    } else if (id as int) < s0.data@.len() {
                        assert(self.data@[id as int] == s0.data@[id as int]);
                    } else {
                        assert(!s0.node_exists(id));
                        assert(!self.node_exists(id));
                    }
                }

                if cnode_prec == NULL {
                    // node has no predecessor => it is the head => prepend.
                    s0.lemma_prec_none_first(node);
                    assert(node == s0.first);
                    assert(self.first == new_node);
                    assert(self.prec_of(new_node).is_none());
                    assert forall|id: u32| id != new_node implies
                        #[trigger] self.next_of(id) == s0.next_of(id) by {
                        if id == node {
                        } else if (id as int) < s0.data@.len() {
                            assert(self.data@[id as int] == s0.data@[id as int]);
                        } else {
                            assert(!s0.node_exists(id));
                            assert(!self.node_exists(id));
                        }
                    }
                    assert forall|id: u32| id != new_node && id != node implies
                        #[trigger] self.prec_of(id) == s0.prec_of(id) by {
                        if (id as int) < s0.data@.len() {
                            assert(self.data@[id as int] == s0.data@[id as int]);
                        } else {
                            assert(!s0.node_exists(id));
                            assert(!self.node_exists(id));
                        }
                    }
                    Self::lemma_prepend_preserves(s0, self, node, new_node);
                } else {
                    // splice new_node after cnode_prec (its old successor is `node`).
                    assert(s0.next_of(cnode_prec) == Some(node));   // links_consistent
                    assert(self.next_of(cnode_prec) == Some(new_node));
                    assert(node != s0.first);
                    assert(self.first == s0.first);
                    assert(cnode_prec != s0.last) by {
                        if cnode_prec == s0.last {
                            assert(s0.next_of(s0.last) == Some(node));
                            assert(s0.last != NULL);
                            assert(s0.next_of(s0.last).is_none());
                        }
                    }
                    assert forall|id: u32| id != cnode_prec && id != new_node implies
                        #[trigger] self.next_of(id) == s0.next_of(id) by {
                        if id == node {
                        } else if (id as int) < s0.data@.len() {
                            assert(self.data@[id as int] == s0.data@[id as int]);
                        } else {
                            assert(!s0.node_exists(id));
                            assert(!self.node_exists(id));
                        }
                    }
                    assert forall|id: u32| id != new_node && id != node implies
                        #[trigger] self.prec_of(id) == s0.prec_of(id) by {
                        if id == cnode_prec {
                        } else if (id as int) < s0.data@.len() {
                            assert(self.data@[id as int] == s0.data@[id as int]);
                        } else {
                            assert(!s0.node_exists(id));
                            assert(!self.node_exists(id));
                        }
                    }
                    Self::lemma_splice_preserves(s0, self, cnode_prec, new_node, node);
                }

                assert(self.valid_chain());
                assert(self.free_list_wf());
                assert forall|id: u32| s0.node_exists(id) implies #[trigger] self.node_exists(id) by {
                    assert(id != new_node);
                }
            }
            new_node
        }
    }
}

// ===========================================================================
// Acyclicity lemmas (consequences of valid_chain) used by delete
//
// A valid chain ends at `last` (whose next is None), so it cannot contain a
// self-loop or a 2-cycle — otherwise traversal would never reach a terminal
// node. delete relies on these to know prec(node) and next(node) are distinct
// from node and from each other (so its `link(p, n)` never aliases one slot).
// ===========================================================================

impl<T> DoublyLinkedList<T> {
    // If a and b form a cycle a -> b -> a, then from a you only ever reach a or b.
    pub proof fn lemma_cycle_reaches_pair(&self, a: u32, b: u32, x: u32, f: nat)
        requires
            self.next_of(a) == Some(b),
            self.next_of(b) == Some(a),
            self.reaches(a, x, f),
        ensures
            x == a || x == b,
        decreases f,
    {
        if a == x {
        } else {
            self.lemma_cycle_reaches_pair(b, a, x, (f - 1) as nat);
        }
    }

    // No live node is its own successor.
    pub proof fn lemma_no_self_loop(&self, id: u32)
        requires
            self.valid_chain(),
            self.data@.len() <= u32::MAX,
            self.node_exists(id),
        ensures
            self.next_of(id) != Some(id),
    {
        if self.next_of(id) == Some(id) {
            assert(self.reachable(id, self.last));
            let f = choose|f: nat| self.reaches(id, self.last, f);
            self.lemma_cycle_reaches_pair(id, id, self.last, f);
            assert(self.last == id);
            assert(self.last != NULL);
            assert(self.next_of(self.last).is_none());
            assert(false);
        }
    }

    // prec(node) and next(node) cannot be the same live node (no 2-cycle).
    pub proof fn lemma_no_two_cycle(&self, node: u32, m: u32)
        requires
            self.valid_chain(),
            self.data@.len() <= u32::MAX,
            self.node_exists(node),
            self.next_of(node) == Some(m),
            self.prec_of(node) == Some(m),
        ensures
            false,
    {
        assert(self.node_exists(m));
        assert(self.next_of(m) == Some(node));     // links_consistent on prec
        assert(self.reachable(node, self.last));
        let f = choose|f: nat| self.reaches(node, self.last, f);
        self.lemma_cycle_reaches_pair(node, m, self.last, f);
        assert(self.last != NULL);
        assert(self.next_of(self.last).is_none());
        assert(false);
    }

    // A live node with no successor must be the tail.
    pub proof fn lemma_next_none_last(&self, id: u32)
        requires
            self.valid_chain(),
            self.data@.len() <= u32::MAX,
            self.node_exists(id),
            self.next_of(id).is_none(),
        ensures
            id == self.last,
    {
        assert(self.reachable(id, self.last));
        let f = choose|f: nat| self.reaches(id, self.last, f);
        self.lemma_reaches_dead_end(id, self.last, f);
    }
}

// ===========================================================================
// Reachability engine for node removal (delete)
// ===========================================================================

impl<T> DoublyLinkedList<T> {
    // Removing `nd` (pred pp, succ pn) reroutes any path that avoided nd: a
    // pre-path between nodes other than nd survives in post (with the same fuel,
    // since the only structural change skips over nd).
    #[verifier::rlimit(60)]
    pub proof fn lemma_reaches_reroute(
        pre: &DoublyLinkedList<T>,
        post: &DoublyLinkedList<T>,
        nd: u32,
        pp: u32,
        pn: u32,
        a: u32,
        b: u32,
        f: nat,
    )
        requires
            pre.valid_chain(),
            pre.data@.len() <= u32::MAX,
            pre.node_exists(nd),
            pre.prec_of(nd) == (if pp != NULL { Some(pp) } else { None }),
            pre.next_of(nd) == (if pn != NULL { Some(pn) } else { None }),
            pp != NULL ==> post.next_of(pp) == pre.next_of(nd),
            forall|id: u32| id != pp && id != nd ==> #[trigger] post.next_of(id) == pre.next_of(id),
            a != nd,
            b != nd,
            pre.reaches(a, b, f),
        ensures
            post.reaches(a, b, f),
        decreases f,
    {
        if a == b {
        } else {
            assert(pre.next_of(a).is_some());
            let m = pre.next_of(a).unwrap();
            if a == pp {
                assert(pre.next_of(pp) == Some(nd));      // consistency
                assert(m == nd);
                assert(pre.reaches(nd, b, (f - 1) as nat));
                if pn == NULL {
                    pre.lemma_reaches_dead_end(nd, b, (f - 1) as nat);
                }
                assert(pn != NULL);
                pre.lemma_no_self_loop(nd);
                assert(pn != nd);
                assert(pre.reaches(pn, b, (f - 2) as nat));
                Self::lemma_reaches_reroute(pre, post, nd, pp, pn, pn, b, (f - 2) as nat);
                assert(post.next_of(pp) == Some(pn));
                post.lemma_reaches_step(pp, pn, b, (f - 2) as nat);
                post.lemma_reaches_fuel_mono(pp, b, (f - 1) as nat, f);
            } else {
                assert(m != nd) by {
                    if m == nd {
                        assert(pre.prec_of(nd) == Some(a));   // consistency
                    }
                }
                assert(post.next_of(a) == pre.next_of(a));
                assert(pre.reaches(m, b, (f - 1) as nat));
                Self::lemma_reaches_reroute(pre, post, nd, pp, pn, m, b, (f - 1) as nat);
                post.lemma_reaches_step(a, m, b, (f - 1) as nat);
            }
        }
    }

    // A pre-path that ENDS at the removed node `nd` reroutes to end at nd's
    // predecessor `pp` in post (the last hop into nd came from pp).
    #[verifier::rlimit(60)]
    pub proof fn lemma_reaches_to_unlinked(
        pre: &DoublyLinkedList<T>,
        post: &DoublyLinkedList<T>,
        nd: u32,
        pp: u32,
        pn: u32,
        a: u32,
        f: nat,
    )
        requires
            pre.valid_chain(),
            pre.data@.len() <= u32::MAX,
            pre.node_exists(nd),
            pp != NULL,
            pre.prec_of(nd) == Some(pp),
            pre.next_of(nd) == (if pn != NULL { Some(pn) } else { None }),
            post.next_of(pp) == pre.next_of(nd),
            forall|id: u32| id != pp && id != nd ==> #[trigger] post.next_of(id) == pre.next_of(id),
            a != nd,
            pre.reaches(a, nd, f),
        ensures
            post.reaches(a, pp, f),
        decreases f,
    {
        assert(pre.next_of(a).is_some());
        let m = pre.next_of(a).unwrap();
        if m == nd {
            assert(pre.prec_of(nd) == Some(a));     // consistency
            assert(a == pp);
            assert(post.reaches(pp, pp, 0));
            post.lemma_reaches_fuel_mono(pp, pp, 0, f);
        } else {
            assert(pre.reaches(m, nd, (f - 1) as nat));
            Self::lemma_reaches_to_unlinked(pre, post, nd, pp, pn, m, (f - 1) as nat);
            assert(a != pp) by {
                if a == pp {
                    assert(pre.next_of(pp) == Some(nd));   // consistency
                }
            }
            assert(post.next_of(a) == pre.next_of(a));
            post.lemma_reaches_step(a, m, pp, (f - 1) as nat);
        }
    }

    // Removing live node `nd` (pred pp, succ pn) preserves the whole chain.
    #[verifier::rlimit(100)]
    pub proof fn lemma_unlink_preserves(
        pre: &DoublyLinkedList<T>,
        post: &DoublyLinkedList<T>,
        nd: u32,
        pp: u32,
        pn: u32,
    )
        requires
            pre.valid_chain(),
            pre.data@.len() <= u32::MAX,
            pre.node_exists(nd),
            pp == pre.elem(nd).prec,
            pn == pre.elem(nd).next,
            !post.node_exists(nd),
            forall|id: u32| id != nd ==> ((#[trigger] post.node_exists(id)) <==> pre.node_exists(id)),
            pp != NULL ==> post.next_of(pp) == pre.next_of(nd),
            forall|id: u32| id != pp && id != nd ==> #[trigger] post.next_of(id) == pre.next_of(id),
            pn != NULL ==> post.prec_of(pn) == pre.prec_of(nd),
            forall|id: u32| id != pn && id != nd ==> #[trigger] post.prec_of(id) == pre.prec_of(id),
            post.first == (if nd == pre.first { pn } else { pre.first }),
            post.last == (if nd == pre.last { pp } else { pre.last }),
        ensures
            post.valid_chain(),
    {
        assert(pre.first != NULL);
        assert(pre.prec_of(nd) == (if pp != NULL { Some(pp) } else { None }));
        assert(pre.next_of(nd) == (if pn != NULL { Some(pn) } else { None }));
        pre.lemma_no_self_loop(nd);
        if pn != NULL {
            assert(pn != nd);
            assert(pre.node_exists(pn));
        }
        if pp != NULL {
            assert(pre.next_of(pp) == Some(nd));     // consistency
            assert(pp != nd);
            assert(pre.node_exists(pp));
        }
        if pp != NULL && pn != NULL && pp == pn {
            pre.lemma_no_two_cycle(nd, pp);
        }

        if pp == NULL && pn == NULL {
            // nd is isolated => the only node => post is empty.
            pre.lemma_prec_none_first(nd);
            pre.lemma_next_none_last(nd);
            assert(nd == pre.first && nd == pre.last);
            assert(post.first == NULL && post.last == NULL);
            assert forall|id: u32| !(#[trigger] post.node_exists(id)) by {
                if id != nd && pre.node_exists(id) {
                    assert(pre.reachable(pre.first, id));
                    let g = choose|g: nat| pre.reaches(pre.first, id, g);
                    pre.lemma_reaches_dead_end(nd, id, g);
                }
            }
            assert(post.valid_chain());
        } else {
            assert(post.first != NULL) by {
                if nd == pre.first {
                    assert(pp == NULL);
                    assert(pn != NULL);
                }
            }
            assert(post.last != NULL) by {
                if nd == pre.last {
                    assert(pn == NULL);
                    assert(pp != NULL);
                }
            }
            assert(post.node_exists(post.first));
            assert(post.node_exists(post.last));

            assert(post.endpoints_wf()) by {
                if nd == pre.first {
                    assert(post.first == pn);
                    assert(post.prec_of(pn) == pre.prec_of(nd));
                } else {
                    assert(post.first == pre.first);
                    assert(pn != pre.first) by {
                        if pn != NULL && pn == pre.first {
                            assert(pre.prec_of(pn) == Some(nd));
                        }
                    }
                }
                if nd == pre.last {
                    assert(post.last == pp);
                    assert(post.next_of(pp) == pre.next_of(nd));
                } else {
                    assert(post.last == pre.last);
                    assert(pp != pre.last) by {
                        if pp != NULL && pp == pre.last {
                            assert(pre.next_of(pp) == Some(nd));
                        }
                    }
                }
            }

            assert forall|id: u32| #[trigger] post.node_exists(id) implies {
                &&& (post.next_of(id).is_some() ==> post.node_exists(post.next_of(id).unwrap()))
                &&& (post.prec_of(id).is_some() ==> post.node_exists(post.prec_of(id).unwrap()))
                &&& (post.next_of(id).is_some() ==> post.prec_of(post.next_of(id).unwrap()) == Some(id))
                &&& (post.prec_of(id).is_some() ==> post.next_of(post.prec_of(id).unwrap()) == Some(id))
            } by {
                assert(id != nd);
                assert(pre.node_exists(id));
                if id == pp {
                } else if pn != NULL && id == pn {
                } else {
                    assert(post.next_of(id) == pre.next_of(id));
                    assert(post.prec_of(id) == pre.prec_of(id));
                }
            }

            assert forall|id: u32| #[trigger] post.node_exists(id)
                implies post.reachable(post.first, id) by {
                assert(pre.node_exists(id) && id != nd);
                if nd == pre.first {
                    assert(pre.reachable(pre.first, id));
                    let g = choose|g: nat| pre.reaches(pre.first, id, g);
                    assert(pre.reaches(pn, id, (g - 1) as nat));
                    Self::lemma_reaches_reroute(pre, post, nd, pp, pn, pn, id, (g - 1) as nat);
                } else {
                    assert(pre.reachable(pre.first, id));
                    let g = choose|g: nat| pre.reaches(pre.first, id, g);
                    Self::lemma_reaches_reroute(pre, post, nd, pp, pn, pre.first, id, g);
                }
            }

            assert forall|id: u32| #[trigger] post.node_exists(id)
                implies post.reachable(id, post.last) by {
                assert(pre.node_exists(id) && id != nd);
                if nd == pre.last {
                    assert(pre.reachable(id, pre.last));
                    let g = choose|g: nat| pre.reaches(id, pre.last, g);
                    Self::lemma_reaches_to_unlinked(pre, post, nd, pp, pn, id, g);
                } else {
                    assert(pre.reachable(id, pre.last));
                    let g = choose|g: nat| pre.reaches(id, pre.last, g);
                    Self::lemma_reaches_reroute(pre, post, nd, pp, pn, id, pre.last, g);
                }
            }

            assert(post.valid_chain());
        }
    }
}

// ===========================================================================
// delete — verified BEHAVIOR (against the implementation)
//
// Unlinks `node`: rewires its neighbours to each other, fixes head/tail, frees
// the slot. We prove the full unlink behavior and that the free list stays
// well-formed. (Reachability-chain preservation across a removal is the
// heavier proof discussed in the report.)
// ===========================================================================

impl<T> DoublyLinkedList<T> {
    unsafe fn delete(&mut self, node: u32)
        requires
            old(self).wf(),
            old(self).data@.len() <= u32::MAX,
            old(self).node_exists(node),
        ensures
            final(self).wf(),
            final(self).data@.len() == old(self).data@.len(),
            !final(self).node_exists(node),
            forall|id: u32| id != node && old(self).node_exists(id)
                ==> #[trigger] final(self).node_exists(id),
            old(self).elem(node).prec != NULL ==> {
                &&& final(self).node_exists(old(self).elem(node).prec)
                &&& final(self).elem(old(self).elem(node).prec).next == old(self).elem(node).next
            },
            old(self).elem(node).next != NULL ==> {
                &&& final(self).node_exists(old(self).elem(node).next)
                &&& final(self).elem(old(self).elem(node).next).prec == old(self).elem(node).prec
            },
            old(self).first == node ==> final(self).first == old(self).elem(node).next,
            old(self).first != node ==> final(self).first == old(self).first,
            old(self).last == node ==> final(self).last == old(self).elem(node).prec,
            old(self).last != node ==> final(self).last == old(self).last,
    {
        let count = self.data.len();
        if node as usize >= count {
            proof {
                assert(self.node_exists(node));
                assert((node as int) < self.data@.len());
                assert(false);
            }
            return;
        }
        let p;
        let n;
        match self.data[node as usize].as_ref() {
            Some(elem) => {
                p = elem.prec;
                n = elem.next;
            }
            None => {
                proof { assert(false); }
                p = NULL;
                n = NULL;
            }
        }
        proof {
            assert(p == old(self).elem(node).prec);
            assert(n == old(self).elem(node).next);
            // p, n are live (or NULL) and distinct from node and each other.
            if p != NULL {
                assert(self.prec_of(node) == Some(p));
                assert(self.node_exists(p));
                self.lemma_no_self_loop(node);
                assert(p != node);
            }
            if n != NULL {
                assert(self.next_of(node) == Some(n));
                assert(self.node_exists(n));
                self.lemma_no_self_loop(node);
                assert(n != node);
            }
            if p == n && p != NULL {
                assert(self.next_of(node) == Some(n));
                assert(self.prec_of(node) == Some(p));
                self.lemma_no_two_cycle(node, p);
            }
        }
        self.link(p, n);
        let ghost d_link = self.data@;
        if node == self.first {
            self.first = n;
        }
        if node == self.last {
            self.last = p;
        }
        self.data.set(node as usize, None);
        self.free_list.push(node);
        proof {
            let s0 = old(self);
            assert(!self.node_exists(node));
            assert(self.data@.len() == s0.data@.len());

            // Slot-level facts after link + None-write.
            if p != NULL {
                assert(self.data@[p as int] == d_link[p as int]);   // set hit only `node`
                assert(self.node_exists(p));
                assert(self.elem(p).next == n);
                assert(self.elem(p).prec == s0.elem(p).prec);
                assert(self.next_of(p) == s0.next_of(node));
            }
            if n != NULL {
                assert(self.data@[n as int] == d_link[n as int]);
                assert(self.node_exists(n));
                assert(self.elem(n).prec == p);
                assert(self.elem(n).next == s0.elem(n).next);
                assert(self.prec_of(n) == s0.prec_of(node));
            }

            // Existence / next / prec frames feeding lemma_unlink_preserves.
            assert forall|id: u32| id != node implies
                (#[trigger] self.node_exists(id)) <==> s0.node_exists(id) by {
                if p != NULL && id == p {
                } else if n != NULL && id == n {
                } else if (id as int) < s0.data@.len() {
                    assert(self.data@[id as int] == d_link[id as int]);
                    assert(d_link[id as int] == s0.data@[id as int]);
                } else {
                    assert(!s0.node_exists(id));
                    assert(!self.node_exists(id));
                }
            }
            assert forall|id: u32| id != p && id != node implies
                #[trigger] self.next_of(id) == s0.next_of(id) by {
                if n != NULL && id == n {
                } else if (id as int) < s0.data@.len() {
                    assert(self.data@[id as int] == d_link[id as int]);
                    assert(d_link[id as int] == s0.data@[id as int]);
                } else {
                    assert(!s0.node_exists(id));
                    assert(!self.node_exists(id));
                }
            }
            assert forall|id: u32| id != n && id != node implies
                #[trigger] self.prec_of(id) == s0.prec_of(id) by {
                if p != NULL && id == p {
                } else if (id as int) < s0.data@.len() {
                    assert(self.data@[id as int] == d_link[id as int]);
                    assert(d_link[id as int] == s0.data@[id as int]);
                } else {
                    assert(!s0.node_exists(id));
                    assert(!self.node_exists(id));
                }
            }

            Self::lemma_unlink_preserves(s0, self, node, p, n);
            assert(self.valid_chain());

            // survivors: any other old node keeps its slot (link touched only p/n,
            // which stay live; the None write hit only `node`).
            assert forall|id: u32| id != node && s0.node_exists(id)
                implies #[trigger] self.node_exists(id) by {
            }

            // free_list_wf: old free indices still point at holes (distinct from the
            // touched live nodes p/n and from `node`); `node` is now a fresh hole and
            // was not previously free (it was live).
            assert forall|i: int| 0 <= i < self.free_list@.len() implies
                0 <= #[trigger] self.free_list@[i] < self.data@.len()
                    && self.data@[self.free_list@[i] as int].is_none()
            by {
                if i < s0.free_list@.len() {
                    assert(self.free_list@[i] == s0.free_list@[i]);
                    assert(s0.data@[s0.free_list@[i] as int].is_none());
                    assert(s0.free_list@[i] != node);
                } else {
                    assert(self.free_list@[i] == node);
                }
            }
            assert forall|i: int, j: int|
                0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() && i != j
                implies self.free_list@[i] != self.free_list@[j] by {
                if i < s0.free_list@.len() && j < s0.free_list@.len() {
                    assert(self.free_list@[i] == s0.free_list@[i]);
                    assert(self.free_list@[j] == s0.free_list@[j]);
                } else {
                    assert(s0.data@[node as int].is_some());
                }
            }
        }
    }
}

// ===========================================================================
// value_mut — mutable accessor (verified against the implementation)
// ===========================================================================

impl<T> DoublyLinkedList<T> {
    fn value_mut(&mut self, node: u32) -> (result: Option<&mut T>)
        ensures
            result.is_some() == old(self).node_exists(node),
    {
        let index = node as usize;
        if index < self.data.len() {
            match &mut self.data[index] {
                Some(e) => Some(&mut e.value),
                None => None,
            }
        } else {
            None
        }
    }
}

fn main() {}

} // verus!
