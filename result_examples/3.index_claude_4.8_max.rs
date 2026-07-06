// =============================================================================
// Verus specification + proof for an index-based Doubly Linked List.
//
// Source implementation: index_impl.orig.rs:1-230
// Target property:        reachability-based chain validity
//
// Chain validity is stated purely in terms of FORWARD reachability over `next`:
//   * every live node is reachable from `first` by following `next`, and
//   * from every live node, `last` is reachable by following `next`.
// (No mirrored prev-reachability is used in the property itself.)
// =============================================================================
use vstd::prelude::*;

verus! {

// `u32::MAX` is the "null" sentinel used by the implementation for node refs.
pub open spec fn null() -> u32 { 0xffff_ffffu32 }

// -----------------------------------------------------------------------------
// Data structure (concrete fields preserved from the implementation; the
// allocator + lifetime are dropped per the simplified-structure rule, and a
// ghost `order` field is ADDED to witness the abstract node ordering).
// -----------------------------------------------------------------------------
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
    // Ghost witness: the live node indices in list order, first .. last.
    pub order: Ghost<Seq<int>>,
}

impl<T> DoublyLinkedList<T> {
    // -------------------------------------------------------------------------
    // Abstract observations over the concrete storage.
    // -------------------------------------------------------------------------

    /// A slot `i` is a live node iff it is in range and holds `Some`.
    pub open spec fn slive(self, i: int) -> bool {
        0 <= i < self.data.len() && self.data@[i] is Some
    }

    /// The `next` field of a live node, as `int` (recommends live).
    pub open spec fn snext(self, i: int) -> int
        recommends self.slive(i)
    {
        self.data@[i]->Some_0.next as int
    }

    /// The `prec` field of a live node, as `int` (recommends live).
    pub open spec fn sprec(self, i: int) -> int
        recommends self.slive(i)
    {
        self.data@[i]->Some_0.prec as int
    }

    /// The stored value of a live node (recommends live).
    pub open spec fn sval(self, i: int) -> T
        recommends self.slive(i)
    {
        self.data@[i]->Some_0.value
    }

    /// Abstract successor: `None` past the end (or for dead nodes).
    pub open spec fn next_of(self, i: int) -> Option<int> {
        if self.slive(i) && self.snext(i) != null() as int {
            Some(self.snext(i))
        } else {
            None
        }
    }

    /// Abstract predecessor: `None` before the start (or for dead nodes).
    pub open spec fn prev_of(self, i: int) -> Option<int> {
        if self.slive(i) && self.sprec(i) != null() as int {
            Some(self.sprec(i))
        } else {
            None
        }
    }

    /// `first` as an abstract optional node.
    pub open spec fn first_opt(self) -> Option<int> {
        if self.first != null() { Some(self.first as int) } else { None }
    }

    /// `last` as an abstract optional node.
    pub open spec fn last_opt(self) -> Option<int> {
        if self.last != null() { Some(self.last as int) } else { None }
    }

    /// The abstract set of nodes is exactly the set of indices in `order`.
    pub open spec fn nodes(self) -> Set<int> {
        self.order@.to_set()
    }

    // -------------------------------------------------------------------------
    // Forward reachability via `next` (existential over a step count).
    // -------------------------------------------------------------------------

    /// `b` reachable from `a` in exactly `fuel` `next`-steps (or fewer, if it
    /// lands on `b` early).
    pub open spec fn reaches_in(self, a: int, b: int, fuel: nat) -> bool
        decreases fuel
    {
        if a == b {
            true
        } else if fuel == 0 {
            false
        } else {
            match self.next_of(a) {
                Some(c) => self.reaches_in(c, b, (fuel - 1) as nat),
                None => false,
            }
        }
    }

    /// `b` reachable from `a` by following `next` some finite number of times.
    pub open spec fn reaches(self, a: int, b: int) -> bool {
        exists|fuel: nat| self.reaches_in(a, b, fuel)
    }

    // -------------------------------------------------------------------------
    // Strong, inductive representation invariant.
    //
    // `order` lists the live nodes in chain order; the storage links agree with
    // it in both directions; `first`/`last` are the endpoints; and `free_list`
    // holds only dead, in-range, distinct slots.  This invariant is maintained
    // by every operation and (see `lemma_inv_valid`) implies `valid_chain`.
    // -------------------------------------------------------------------------
    pub open spec fn inv(self) -> bool {
        let ord = self.order@;
        &&& self.data.len() < null() as int
        // order entries are live indices
        &&& (forall|k: int| 0 <= k < ord.len() ==> self.slive(#[trigger] ord[k]))
        // every live node appears in order
        &&& (forall|i: int| self.slive(i) ==> #[trigger] ord.contains(i))
        // order has no duplicates
        &&& (forall|k1: int, k2: int|
                0 <= k1 < ord.len() && 0 <= k2 < ord.len() && ord[k1] == ord[k2] ==> k1 == k2)
        // endpoints
        &&& (ord.len() == 0 ==> self.first == null() && self.last == null())
        &&& (ord.len() > 0 ==> self.first as int == ord[0] && self.last as int == ord[ord.len() - 1])
        // forward links agree with order
        &&& (forall|k: int| 0 <= k < ord.len() - 1 ==> self.snext(#[trigger] ord[k]) == ord[k + 1])
        &&& (ord.len() > 0 ==> self.snext(ord[ord.len() - 1]) == null() as int)
        // backward links agree with order (bidirectional consistency)
        &&& (forall|k: int| 1 <= k < ord.len() ==> self.sprec(#[trigger] ord[k]) == ord[k - 1])
        &&& (ord.len() > 0 ==> self.sprec(ord[0]) == null() as int)
        // free_list: dead, in range, distinct
        &&& (forall|j: int| 0 <= j < self.free_list.len() ==> {
                let f = #[trigger] self.free_list@[j] as int;
                0 <= f < self.data.len() && self.data@[f] is None
            })
        &&& (forall|j1: int, j2: int|
                0 <= j1 < self.free_list.len() && 0 <= j2 < self.free_list.len()
                && self.free_list@[j1] == self.free_list@[j2] ==> j1 == j2)
    }

    // -------------------------------------------------------------------------
    // The target property: reachability-based chain validity.
    // -------------------------------------------------------------------------
    pub open spec fn valid_chain(self) -> bool {
        &&& (self.first == null() <==> self.order@.len() == 0)
        &&& (self.last == null() <==> self.order@.len() == 0)
        &&& (self.first != null() ==> self.nodes().contains(self.first as int))
        &&& (self.last != null() ==> self.nodes().contains(self.last as int))
        // every node reachable from `first` via `next`
        &&& (forall|i: int| #[trigger] self.nodes().contains(i) ==> self.reaches(self.first as int, i))
        // from every node, `last` reachable via `next`
        &&& (forall|i: int| #[trigger] self.nodes().contains(i) ==> self.reaches(i, self.last as int))
    }
}

// =============================================================================
// Reachability lemmas: `inv` implies `valid_chain`.
// =============================================================================
impl<T> DoublyLinkedList<T> {
    /// Walking forward along `order` from position `j` to position `k` is a
    /// witnessed reachability of exactly `k - j` steps.
    pub proof fn lemma_forward(&self, j: int, k: int)
        requires
            self.inv(),
            0 <= j <= k < self.order@.len(),
        ensures
            self.reaches_in(self.order@[j], self.order@[k], (k - j) as nat),
        decreases k - j
    {
        let ord = self.order@;
        if j == k {
            assert(self.reaches_in(ord[j], ord[k], 0));
        } else {
            // j < k: step from ord[j] to ord[j+1], then recurse.
            assert(self.slive(ord[j]));
            assert(self.snext(ord[j]) == ord[j + 1]);  // forward-link invariant
            assert(self.slive(ord[j + 1]));            // order entries are live
            assert(0 <= ord[j + 1] < self.data.len()); // hence in range
            assert(ord[j + 1] != null() as int);       // since len < null()
            assert(self.next_of(ord[j]) == Some(ord[j + 1]));
            assert(ord[j] != ord[k]);                  // distinctness, j != k
            self.lemma_forward(j + 1, k);
            assert((k - j) as nat > 0);
            assert(self.reaches_in(ord[j], ord[k], (k - j) as nat));
        }
    }

    /// `inv` establishes the reachability-based chain validity property.
    pub proof fn lemma_inv_valid(&self)
        requires self.inv(),
        ensures self.valid_chain(),
    {
        let ord = self.order@;

        // Endpoints vs emptiness.
        if ord.len() == 0 {
            assert(self.first == null() && self.last == null());
        } else {
            assert(self.first as int == ord[0]);
            assert(self.slive(ord[0]));
            assert(0 <= ord[0] < self.data.len());
            assert(self.first != null());
            assert(self.last as int == ord[ord.len() - 1]);
            assert(self.slive(ord[ord.len() - 1]));
            assert(self.last != null());
        }

        // first/last membership.
        if self.first != null() {
            assert(ord.len() > 0);
            assert(ord[0] == self.first as int);
            assert(ord.contains(self.first as int));
        }
        if self.last != null() {
            assert(ord.len() > 0);
            assert(ord[ord.len() - 1] == self.last as int);
            assert(ord.contains(self.last as int));
        }

        // Reachability from first to every node.
        assert forall|i: int| self.nodes().contains(i) implies #[trigger] self.reaches(
            self.first as int,
            i,
        ) by {
            assert(ord.contains(i));
            let k = choose|k: int| 0 <= k < ord.len() && ord[k] == i;
            assert(0 <= k < ord.len() && ord[k] == i);
            self.lemma_forward(0, k);
            assert(self.first as int == ord[0]);
            assert(self.reaches_in(self.first as int, i, (k - 0) as nat));
        }

        // Reachability from every node to last.
        assert forall|i: int| self.nodes().contains(i) implies #[trigger] self.reaches(
            i,
            self.last as int,
        ) by {
            assert(ord.contains(i));
            let k = choose|k: int| 0 <= k < ord.len() && ord[k] == i;
            assert(0 <= k < ord.len() && ord[k] == i);
            self.lemma_forward(k, ord.len() - 1);
            assert(self.last as int == ord[ord.len() - 1]);
            assert(self.reaches_in(i, self.last as int, (ord.len() - 1 - k) as nat));
        }
    }
}

// =============================================================================
// Constructor + read-only accessors.
// =============================================================================
impl<T> DoublyLinkedList<T> {
    /// Create an empty list.  (The `capacity` hint is accepted for signature
    /// fidelity; it does not affect the abstract state.)
    pub fn new(capacity: usize) -> (r: Self)
        ensures
            r.inv(),
            r.valid_chain(),
            r.order@.len() == 0,
    {
        let _ = capacity;
        let r = DoublyLinkedList {
            data: Vec::new(),
            free_list: Vec::new(),
            first: u32::MAX,
            last: u32::MAX,
            order: Ghost(Seq::empty()),
        };
        proof { r.lemma_inv_valid(); }
        r
    }

    /// Borrow the element at `handle`, if it is a live node.
    fn element(&self, handle: u32) -> (r: Option<&Element<T>>)
        ensures
            self.slive(handle as int) ==> (r is Some && r->Some_0 == self.data@[handle as int]->Some_0),
            !self.slive(handle as int) ==> r is None,
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

    /// First node, or `None` if empty.
    pub fn first(&self) -> (r: Option<u32>)
        ensures
            self.first == null() ==> r is None,
            self.first != null() ==> r == Some(self.first),
    {
        if self.first != u32::MAX {
            Some(self.first)
        } else {
            None
        }
    }

    /// Last node, or `None` if empty.
    pub fn last(&self) -> (r: Option<u32>)
        ensures
            self.last == null() ==> r is None,
            self.last != null() ==> r == Some(self.last),
    {
        if self.last != u32::MAX {
            Some(self.last)
        } else {
            None
        }
    }

    /// Successor of `node` (forward `next` observation).
    pub fn next(&self, node: u32) -> (r: Option<u32>)
        ensures
            match r {
                Some(x) => self.slive(node as int) && self.data@[node as int]->Some_0.next == x
                    && x != null(),
                None => !self.slive(node as int) || self.data@[node as int]->Some_0.next == null(),
            },
    {
        if let Some(e) = self.element(node) {
            if e.next != u32::MAX {
                Some(e.next)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Predecessor of `node` (backward `prec` observation).
    pub fn prec(&self, node: u32) -> (r: Option<u32>)
        ensures
            match r {
                Some(x) => self.slive(node as int) && self.data@[node as int]->Some_0.prec == x
                    && x != null(),
                None => !self.slive(node as int) || self.data@[node as int]->Some_0.prec == null(),
            },
    {
        if let Some(e) = self.element(node) {
            if e.prec != u32::MAX {
                Some(e.prec)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Shared reference to the value stored at `node`.
    pub fn value(&self, node: u32) -> (r: Option<&T>)
        ensures
            match r {
                Some(v) => self.slive(node as int) && *v == self.sval(node as int),
                None => !self.slive(node as int),
            },
    {
        if let Some(e) = self.element(node) {
            Some(&e.value)
        } else {
            None
        }
    }

    /// True iff the list has no live nodes.  Scans storage like the original,
    /// but its result is proven equivalent to "the abstract list is empty".
    pub fn is_empty(&self) -> (r: bool)
        requires self.inv(),
        ensures r <==> (self.order@.len() == 0),
    {
        let mut i: usize = 0;
        while i < self.data.len()
            invariant
                0 <= i <= self.data.len(),
                self.inv(),
                forall|j: int| 0 <= j < i ==> self.data@[j] is None,
            decreases self.data.len() - i,
        {
            if self.data[i].is_some() {
                assert(self.slive(i as int));
                assert(self.order@.contains(i as int));
                assert(self.order@.len() > 0);
                return false;
            }
            i = i + 1;
        }
        // No live slot found anywhere; hence `order` must be empty.
        proof {
            if self.order@.len() > 0 {
                assert(self.slive(self.order@[0]));     // from inv
                assert(0 <= self.order@[0] < self.data.len());
                assert(self.data@[self.order@[0]] is None);  // from loop post
                assert(false);
            }
        }
        true
    }
}

// =============================================================================
// Internal mutating helpers.
// =============================================================================
impl<T> DoublyLinkedList<T> {
    /// Obtain a fresh, dead slot (reusing a freed one if available, else
    /// appending) and initialise it as an isolated live node (next/prec = null).
    fn allocate(&mut self, value: T) -> (r: u32)
        requires
            old(self).inv(),
            old(self).data.len() < u32::MAX as int - 1,
        ensures
            old(self).data.len() <= final(self).data.len() <= old(self).data.len() + 1,
            final(self).data.len() < u32::MAX as int,
            (r as int) < final(self).data.len(),
            r != null(),
            final(self).slive(r as int),
            final(self).data@[r as int]->Some_0.next == null(),
            final(self).data@[r as int]->Some_0.prec == null(),
            final(self).data@[r as int]->Some_0.value == value,
            !old(self).slive(r as int),
            !old(self).order@.contains(r as int),
            final(self).order@ == old(self).order@,
            final(self).first == old(self).first,
            final(self).last == old(self).last,
            forall|i: int|
                0 <= i < old(self).data.len() && i != r as int
                    ==> final(self).data@[i] == old(self).data@[i],
            // if the vector grew, the fresh slot is exactly the new last index
            final(self).data.len() == old(self).data.len() + 1 ==> r as int == old(self).data.len(),
            forall|j: int| 0 <= j < final(self).free_list.len() ==> {
                let f = #[trigger] final(self).free_list@[j] as int;
                0 <= f < final(self).data.len() && f != r as int && final(self).data@[f] is None
            },
            forall|j1: int, j2: int|
                0 <= j1 < final(self).free_list.len() && 0 <= j2 < final(self).free_list.len()
                    && final(self).free_list@[j1] == final(self).free_list@[j2] ==> j1 == j2,
    {
        let allocated: usize = self.data.len();
        let new_elem = Element { next: u32::MAX, prec: u32::MAX, value };
        let ghost old_self = *self;
        match self.free_list.pop() {
            Some(f) => {
                assert(old_self.free_list@.len() > 0);
                assert(f == old_self.free_list@[old_self.free_list@.len() - 1]);
                assert((f as int) < allocated);            // free_list entries in range
                assert(old_self.data@[f as int] is None);  // free_list entries dead
                self.data.set(f as usize, Some(new_elem));
                proof {
                    // freshness: f was dead, so not in order
                    assert(!old_self.slive(f as int));
                    if old_self.order@.contains(f as int) {
                        let k = choose|k: int|
                            0 <= k < old_self.order@.len() && old_self.order@[k] == f as int;
                        assert(old_self.slive(old_self.order@[k]));
                        assert(false);
                    }
                    // free_list well-formedness after drop_last
                    assert forall|j: int| 0 <= j < self.free_list.len() implies {
                        let g = #[trigger] self.free_list@[j] as int;
                        0 <= g < self.data.len() && g != f as int && self.data@[g] is None
                    } by {
                        assert(self.free_list@[j] == old_self.free_list@[j]);
                        // distinctness => entry j (j < len-1) differs from popped f
                        assert(self.free_list@[j] != f);
                        assert(old_self.data@[self.free_list@[j] as int] is None);
                    }
                }
                f
            }
            None => {
                assert(old_self.free_list@.len() == 0);
                self.data.push(Some(new_elem));
                proof {
                    assert(!old_self.slive(allocated as int));
                    if old_self.order@.contains(allocated as int) {
                        let k = choose|k: int|
                            0 <= k < old_self.order@.len() && old_self.order@[k] == allocated as int;
                        assert(old_self.slive(old_self.order@[k]));
                        assert(false);
                    }
                }
                allocated as u32
            }
        }
    }

    /// Set `next(n1) := n2` and `prec(n2) := n1`, ignoring out-of-range
    /// endpoints (the `u32::MAX` sentinel).
    fn link(&mut self, n1: u32, n2: u32)
        requires
            old(self).data.len() < u32::MAX as int,
            (n1 as int) < old(self).data.len() ==> old(self).data@[n1 as int] is Some,
            (n2 as int) < old(self).data.len() ==> old(self).data@[n2 as int] is Some,
            (n1 as int) < old(self).data.len() && (n2 as int) < old(self).data.len() ==> n1 != n2,
        ensures
            final(self).data.len() == old(self).data.len(),
            final(self).free_list == old(self).free_list,
            final(self).first == old(self).first,
            final(self).last == old(self).last,
            final(self).order@ == old(self).order@,
            (n1 as int) < old(self).data.len() ==> (
                final(self).data@[n1 as int] is Some
                    && final(self).data@[n1 as int]->Some_0.next == n2
                    && final(self).data@[n1 as int]->Some_0.prec
                        == old(self).data@[n1 as int]->Some_0.prec
                    && final(self).data@[n1 as int]->Some_0.value
                        == old(self).data@[n1 as int]->Some_0.value
            ),
            (n2 as int) < old(self).data.len() ==> (
                final(self).data@[n2 as int] is Some
                    && final(self).data@[n2 as int]->Some_0.prec == n1
                    && final(self).data@[n2 as int]->Some_0.next
                        == old(self).data@[n2 as int]->Some_0.next
                    && final(self).data@[n2 as int]->Some_0.value
                        == old(self).data@[n2 as int]->Some_0.value
            ),
            forall|i: int|
                0 <= i < old(self).data.len() && i != n1 as int && i != n2 as int
                    ==> final(self).data@[i] == old(self).data@[i],
    {
        let count = self.data.len();
        let idx1 = n1 as usize;
        let idx2 = n2 as usize;
        let ghost old_self = *self;
        if idx1 < count {
            let mut e1 = self.data[idx1].take().unwrap();
            e1.next = n2;
            self.data.set(idx1, Some(e1));
        }
        if idx2 < count {
            assert(self.data@[idx2 as int] == old_self.data@[idx2 as int]);  // idx2 != idx1
            let mut e2 = self.data[idx2].take().unwrap();
            e2.prec = n1;
            self.data.set(idx2, Some(e2));
        }
    }

    /// Insert the first element of a (logically) empty list.
    ///
    /// NOTE: this differs from the original implementation, which pushed a new
    /// slot and unconditionally set `first = last = 0`.  That is only correct
    /// when `data` is physically empty; after deleting every node `data` still
    /// has dead slots, so `0` need not be the new node.  See the discrepancy
    /// report.  The corrected version routes through `allocate`.
    fn add_first_element(&mut self, value: T) -> (r: u32)
        requires
            old(self).inv(),
            old(self).order@.len() == 0,
            old(self).data.len() < u32::MAX as int - 1,
        ensures
            final(self).inv(),
            final(self).order@ == seq![r as int],
            r != null(),
            final(self).slive(r as int),
            final(self).sval(r as int) == value,
            final(self).first == r,
            final(self).last == r,
    {
        let node = self.allocate(value);
        self.first = node;
        self.last = node;
        proof {
            // The empty list (order empty + inv) has no live nodes.
            assert forall|i: int| !old(self).slive(i) by {
                if old(self).slive(i) {
                    assert(old(self).order@.contains(i));  // old inv
                    assert(false);
                }
            }
            self.order@ = seq![node as int];
            let ord = self.order@;
            assert(ord.len() == 1 && ord[0] == node as int);
            // After allocate, `node` is the unique live node.
            assert forall|i: int| self.slive(i) implies #[trigger] ord.contains(i) by {
                if i != node as int {
                    if 0 <= i < old(self).data.len() {
                        assert(self.data@[i] == old(self).data@[i]);
                        assert(!old(self).slive(i));
                        assert(!self.slive(i));
                    } else {
                        // i >= old len; allocate guarantees any such live index is `node`
                        assert(!self.slive(i));
                    }
                    assert(false);
                }
            }
        }
        node
    }
}

// Inserting a fresh element `x` (not already in `s`) at position `j` keeps the
// sequence duplicate-free.
proof fn lemma_insert_distinct(s: Seq<int>, j: int, x: int, k1: int, k2: int)
    requires
        0 <= j <= s.len(),
        forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && s[a] == s[b] ==> a == b,
        forall|a: int| 0 <= a < s.len() ==> s[a] != x,
        0 <= k1 < s.len() + 1,
        0 <= k2 < s.len() + 1,
        s.insert(j, x)[k1] == s.insert(j, x)[k2],
    ensures
        k1 == k2,
{
    let t = s.insert(j, x);
    // value at index i of t: x at j, else s[i] (i<j) or s[i-1] (i>j)
    let v1 = if k1 < j { s[k1] } else if k1 == j { x } else { s[k1 - 1] };
    let v2 = if k2 < j { s[k2] } else if k2 == j { x } else { s[k2 - 1] };
    assert(t[k1] == v1);
    assert(t[k2] == v2);
}

// Removing the element at position `p` from a duplicate-free sequence keeps it
// duplicate-free.
proof fn lemma_remove_distinct(s: Seq<int>, p: int, k1: int, k2: int)
    requires
        0 <= p < s.len(),
        forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && s[a] == s[b] ==> a == b,
        0 <= k1 < s.len() - 1,
        0 <= k2 < s.len() - 1,
        s.remove(p)[k1] == s.remove(p)[k2],
    ensures
        k1 == k2,
{
    let t = s.remove(p);
    let i1 = if k1 < p { k1 } else { k1 + 1 };
    let i2 = if k2 < p { k2 } else { k2 + 1 };
    assert(t[k1] == s[i1]);
    assert(t[k2] == s[i2]);
}

// =============================================================================
// Public mutating operations.
// =============================================================================
impl<T> DoublyLinkedList<T> {
    /// Append `value` as the new last node.
    pub fn push_back(&mut self, value: T) -> (r: u32)
        requires
            old(self).inv(),
            old(self).data.len() < u32::MAX as int - 1,
        ensures
            final(self).inv(),
            final(self).valid_chain(),
            final(self).order@ == old(self).order@.push(r as int),
            r != null(),
            final(self).slive(r as int),
            final(self).sval(r as int) == value,
            final(self).last == r,
            !old(self).order@.contains(r as int),
    {
        let ghost oo = self.order@;
        if self.is_empty() {
            let r = self.add_first_element(value);
            proof {
                assert(oo.len() == 0);
                assert(self.order@ =~= oo.push(r as int));
                self.lemma_inv_valid();
            }
            r
        } else {
            let node = self.allocate(value);
            let ghost s1 = *self;
            let old_last = self.last;
            proof {
                assert(oo.len() > 0);
                assert(old(self).last as int == oo[oo.len() - 1]);  // old inv endpoint
                assert(old(self).slive(oo[oo.len() - 1]));          // old inv liveness
                assert(oo.contains(oo[oo.len() - 1]));
                assert(old_last as int == oo[oo.len() - 1]);
                assert(old_last as int != node as int);             // node fresh
                assert(self.data@[old_last as int] is Some);        // framed by allocate
                assert((node as int) < self.data.len());
            }
            self.link(old_last, node);
            self.last = node;
            proof {
                let ghost L: int = oo.len() as int;
                self.order@ = oo.push(node as int);
                let no = self.order@;
                assert(no.len() == L + 1);
                assert(no[L] == node as int);
                assert(forall|k: int| 0 <= k < L ==> no[k] == oo[k]);
                assert(forall|j: int| 0 <= j < L ==> oo[j] != node as int);  // node not in oo

                // node's links: next stayed null, prec became old_last
                assert(self.data@[node as int]->Some_0.next == null());
                assert(self.data@[node as int]->Some_0.prec == old_last);
                // old_last's link: next became node
                assert(self.snext(old_last as int) == node as int);

                // (b) every order entry is live
                assert forall|k: int| 0 <= k < no.len() implies self.slive(#[trigger] no[k]) by {
                    if k < L {
                        assert(no[k] == oo[k]);
                        assert(old(self).slive(oo[k]));
                        if oo[k] != old_last as int {
                            assert(self.data@[oo[k]] == old(self).data@[oo[k]]);
                        }
                    }
                }
                // (c) every live node is in order
                assert forall|i: int| self.slive(i) implies #[trigger] no.contains(i) by {
                    if i != node as int {
                        if 0 <= i < old(self).data.len() {
                            if i != old_last as int {
                                assert(self.data@[i] == old(self).data@[i]);
                            }
                            assert(old(self).slive(i));
                            assert(old(self).order@.contains(i));
                            let k = choose|k: int|
                                0 <= k < oo.len() && oo[k] == i;
                            assert(no[k] == i);
                        } else {
                            assert(!self.slive(i));
                        }
                    } else {
                        assert(no[L] == i);
                    }
                }
                // (d) distinctness
                assert forall|k1: int, k2: int|
                    0 <= k1 < no.len() && 0 <= k2 < no.len() && no[k1] == no[k2] implies k1 == k2 by {
                    if k1 < L && k2 < L {
                        assert(oo[k1] == oo[k2]);
                    } else if k1 < L && k2 == L {
                        assert(oo[k1] == node as int);  // impossible
                    } else if k1 == L && k2 < L {
                        assert(oo[k2] == node as int);  // impossible
                    }
                }
                // (f) forward links
                assert forall|k: int| 0 <= k < no.len() - 1 implies self.snext(#[trigger] no[k]) == no[k + 1] by {
                    if k < L - 1 {
                        assert(no[k] == oo[k] && no[k + 1] == oo[k + 1]);
                        assert(oo[k] != old_last as int);  // old_last is oo[L-1]
                        assert(self.data@[oo[k]] == old(self).data@[oo[k]]);
                        assert(old(self).snext(oo[k]) == oo[k + 1]);
                    } else {
                        assert(k == L - 1);
                        assert(no[k] == old_last as int && no[k + 1] == node as int);
                    }
                }
                // (h) backward links
                assert forall|k: int| 1 <= k < no.len() implies self.sprec(#[trigger] no[k]) == no[k - 1] by {
                    if k < L {
                        assert(no[k] == oo[k] && no[k - 1] == oo[k - 1]);
                        assert(self.data@[oo[k]]->Some_0.prec == old(self).data@[oo[k]]->Some_0.prec);
                        assert(old(self).sprec(oo[k]) == oo[k - 1]);
                    } else {
                        assert(k == L);
                        assert(no[k] == node as int && no[k - 1] == old_last as int);
                    }
                }
                // free_list entries are still dead and in range (link left them untouched)
                assert forall|j: int| 0 <= j < self.free_list.len() implies {
                    let f = #[trigger] self.free_list@[j] as int;
                    0 <= f < self.data.len() && self.data@[f] is None
                } by {
                    let f = self.free_list@[j] as int;
                    assert(f != node as int);
                    assert(self.data@[f] == s1.data@[f]);  // link framed dead slots
                }

                self.lemma_inv_valid();
            }
            node
        }
    }

    /// Prepend `value` as the new first node.
    pub fn push_front(&mut self, value: T) -> (r: u32)
        requires
            old(self).inv(),
            old(self).data.len() < u32::MAX as int - 1,
        ensures
            final(self).inv(),
            final(self).valid_chain(),
            final(self).order@ == seq![r as int] + old(self).order@,
            r != null(),
            final(self).slive(r as int),
            final(self).sval(r as int) == value,
            final(self).first == r,
            !old(self).order@.contains(r as int),
    {
        let ghost oo = self.order@;
        if self.is_empty() {
            let r = self.add_first_element(value);
            proof {
                assert(oo.len() == 0);
                assert(self.order@ =~= seq![r as int] + oo);
                self.lemma_inv_valid();
            }
            r
        } else {
            let node = self.allocate(value);
            let ghost s1 = *self;
            let old_first = self.first;
            proof {
                assert(oo.len() > 0);
                assert(old(self).first as int == oo[0]);   // old inv endpoint
                assert(old(self).slive(oo[0]));            // old inv liveness
                assert(oo.contains(oo[0]));
                assert(old_first as int == oo[0]);
                assert(old_first as int != node as int);   // node fresh
                assert(self.data@[old_first as int] is Some);
                assert((node as int) < self.data.len());
            }
            self.link(node, old_first);
            self.first = node;
            proof {
                let ghost L: int = oo.len() as int;
                self.order@ = seq![node as int] + oo;
                let no = self.order@;
                assert(no.len() == L + 1);
                assert(no[0] == node as int);
                assert(forall|k: int| 1 <= k < L + 1 ==> no[k] == oo[k - 1]);
                assert(forall|j: int| 0 <= j < L ==> oo[j] != node as int);

                // node's links: prec stayed null, next became old_first
                assert(self.data@[node as int]->Some_0.prec == null());
                assert(self.snext(node as int) == old_first as int);
                // old_first's link: prec became node
                assert(self.sprec(old_first as int) == node as int);

                // (b) every order entry is live
                assert forall|k: int| 0 <= k < no.len() implies self.slive(#[trigger] no[k]) by {
                    if k >= 1 {
                        assert(no[k] == oo[k - 1]);
                        assert(old(self).slive(oo[k - 1]));
                        if oo[k - 1] != old_first as int {
                            assert(self.data@[oo[k - 1]] == old(self).data@[oo[k - 1]]);
                        }
                    }
                }
                // (c) every live node is in order
                assert forall|i: int| self.slive(i) implies #[trigger] no.contains(i) by {
                    if i != node as int {
                        if 0 <= i < old(self).data.len() {
                            if i != old_first as int {
                                assert(self.data@[i] == old(self).data@[i]);
                            }
                            assert(old(self).slive(i));
                            assert(old(self).order@.contains(i));
                            let k = choose|k: int| 0 <= k < oo.len() && oo[k] == i;
                            assert(no[k + 1] == i);
                        } else {
                            assert(!self.slive(i));
                        }
                    } else {
                        assert(no[0] == i);
                    }
                }
                // (d) distinctness
                assert forall|k1: int, k2: int|
                    0 <= k1 < no.len() && 0 <= k2 < no.len() && no[k1] == no[k2] implies k1 == k2 by {
                    if k1 >= 1 && k2 >= 1 {
                        assert(oo[k1 - 1] == oo[k2 - 1]);
                    } else if k1 >= 1 && k2 == 0 {
                        assert(oo[k1 - 1] == node as int);  // impossible
                    } else if k1 == 0 && k2 >= 1 {
                        assert(oo[k2 - 1] == node as int);  // impossible
                    }
                }
                // (f) forward links — `next` of every old node is preserved
                // (link touched only node.next and old_first.prec).
                assert forall|k: int| 0 <= k < no.len() - 1 implies self.snext(#[trigger] no[k]) == no[k + 1] by {
                    if k == 0 {
                        assert(no[0] == node as int && no[1] == oo[0]);
                        assert(oo[0] == old_first as int);
                    } else {
                        assert(no[k] == oo[k - 1] && no[k + 1] == oo[k]);
                        assert(old(self).snext(oo[k - 1]) == oo[k]);
                        assert(oo[k - 1] != node as int);
                        if oo[k - 1] == old_first as int {
                            assert(self.data@[old_first as int]->Some_0.next
                                == s1.data@[old_first as int]->Some_0.next);
                            assert(s1.data@[old_first as int] == old(self).data@[old_first as int]);
                        } else {
                            assert(self.data@[oo[k - 1]] == s1.data@[oo[k - 1]]);
                            assert(s1.data@[oo[k - 1]] == old(self).data@[oo[k - 1]]);
                        }
                    }
                }
                // (h) backward links
                assert(old_first as int == oo[0]);
                assert forall|k: int| 1 <= k < no.len() implies self.sprec(#[trigger] no[k]) == no[k - 1] by {
                    if k == 1 {
                        assert(no[1] == oo[0] && no[0] == node as int);
                        assert(oo[0] == old_first as int);
                    } else {
                        assert(no[k] == oo[k - 1] && no[k - 1] == oo[k - 2]);
                        assert(old(self).sprec(oo[k - 1]) == oo[k - 2]);
                        assert(oo[k - 1] != oo[0]);          // distinctness, k-1 >= 1
                        assert(oo[k - 1] != old_first as int);
                        assert(oo[k - 1] != node as int);
                        assert(self.data@[oo[k - 1]] == old(self).data@[oo[k - 1]]);
                    }
                }
                // free_list entries untouched by link
                assert forall|j: int| 0 <= j < self.free_list.len() implies {
                    let f = #[trigger] self.free_list@[j] as int;
                    0 <= f < self.data.len() && self.data@[f] is None
                } by {
                    let f = self.free_list@[j] as int;
                    assert(f != node as int);
                    assert(self.data@[f] == s1.data@[f]);
                }

                self.lemma_inv_valid();
            }
            node
        }
    }

    /// Insert `value` immediately after the live node `node`.
    ///
    /// The original `is_empty()` / `node == u32::MAX` guards (which `panic`) are
    /// elided: the precondition `slive(node)` makes both branches unreachable
    /// (a live node implies a non-empty list and `node != u32::MAX`).
    #[verifier::spinoff_prover]
    #[verifier::rlimit(100)]
    pub fn insert_after(&mut self, node: u32, value: T) -> (r: u32)
        requires
            old(self).inv(),
            old(self).slive(node as int),
            old(self).data.len() < u32::MAX as int - 1,
        ensures
            final(self).inv(),
            final(self).valid_chain(),
            r != null(),
            final(self).slive(r as int),
            final(self).sval(r as int) == value,
            !old(self).order@.contains(r as int),
            final(self).snext(node as int) == r as int,   // next(node) = new
            final(self).sprec(r as int) == node,           // prec(new)  = node
            exists|p: int|
                #![auto]
                0 <= p < old(self).order@.len() && old(self).order@[p] == node as int
                    && final(self).order@ == old(self).order@.insert(p + 1, r as int),
    {
        let ghost oo = self.order@;
        let ghost L: int = oo.len() as int;
        proof {
            assert(self.order@.contains(node as int));  // node live => in order
        }
        let new_node = self.allocate(value);
        let ghost s1 = *self;
        proof {
            assert(self.data@[node as int] == old(self).data@[node as int]);  // framed
            assert((node as int) < self.data.len());
        }
        let cnode_next = self.data[node as usize].as_ref().unwrap().next;
        proof {
            assert(cnode_next == old(self).data@[node as int]->Some_0.next);
            assert(node as int != new_node as int);
            assert(self.data@[node as int] is Some);
            assert((new_node as int) < self.data.len());
        }
        self.link(node, new_node);
        let ghost s2 = *self;
        proof {
            // establish link2 preconditions
            assert(self.data@[new_node as int] is Some);
            if (cnode_next as int) < self.data.len() {
                // cnode_next is node's old successor, which is live
                assert(self.data@[cnode_next as int] == old(self).data@[cnode_next as int]);
                assert(new_node as int != cnode_next as int);
            }
        }
        self.link(new_node, cnode_next);
        let ghost s3 = *self;
        if node == self.last {
            self.last = new_node;
        }
        proof {
            let ghost p = choose|q: int| 0 <= q < oo.len() && oo[q] == node as int;
            assert(0 <= p < L && oo[p] == node as int);
            self.order@ = oo.insert(p + 1, new_node as int);
            let no = self.order@;
            let ghost new_id = new_node as int;

            assert(no.len() == L + 1);
            assert(no[p + 1] == new_id);
            assert(forall|i: int| 0 <= i <= p ==> no[i] == oo[i]);
            assert(forall|i: int| p + 1 < i <= L ==> no[i] == oo[i - 1]);
            assert(forall|j: int| 0 <= j < L ==> oo[j] != new_id);

            // Per-position field values of the three touched slots.
            assert(self.snext(node as int) == new_id);          // link1
            assert(self.sprec(new_id) == node as int);          // link1
            assert(self.data@[new_id]->Some_0.next == cnode_next);  // link2
            let ghost is_last = (p == L - 1);
            if p < L - 1 {
                assert(old(self).snext(oo[p]) == oo[p + 1]);     // old fwd link
                assert((cnode_next as int) == oo[p + 1]);
                assert(self.slive(oo[p + 1]));
                assert(self.sprec(oo[p + 1]) == new_id);          // link2 set prec
                assert(self.last == old(self).last);
            } else {
                assert(old(self).snext(oo[p]) == null() as int);  // node was last
                assert(cnode_next == null());
                assert(self.snext(new_id) == null() as int);
                assert(self.last == new_node);
            }

            // (b) liveness of every order entry
            assert forall|i: int| 0 <= i < no.len() implies self.slive(#[trigger] no[i]) by {
                if i == p + 1 {
                } else if i <= p {
                    assert(no[i] == oo[i]);
                    assert(old(self).slive(oo[i]));
                    assert(self.data@[oo[i]] is Some);
                } else {
                    assert(no[i] == oo[i - 1]);
                    assert(old(self).slive(oo[i - 1]));
                    assert(self.data@[oo[i - 1]] is Some);
                }
            }
            // (c) every live node is in order
            assert forall|i: int| self.slive(i) implies #[trigger] no.contains(i) by {
                if i != new_id {
                    if 0 <= i < old(self).data.len() {
                        assert(self.data@[i] is Some ==> old(self).data@[i] is Some);
                        assert(old(self).slive(i));
                        assert(old(self).order@.contains(i));
                        let k = choose|k: int| 0 <= k < oo.len() && oo[k] == i;
                        if k <= p {
                            assert(no[k] == i);
                        } else {
                            assert(no[k + 1] == i);
                        }
                    } else {
                        assert(!self.slive(i));
                    }
                } else {
                    assert(no[p + 1] == i);
                }
            }
            // (d) distinctness
            assert forall|k1: int, k2: int|
                0 <= k1 < no.len() && 0 <= k2 < no.len() && no[k1] == no[k2] implies k1 == k2 by {
                lemma_insert_distinct(oo, p, new_id, k1, k2);
            }
            // (f) forward links
            assert forall|i: int| 0 <= i < no.len() - 1 implies self.snext(#[trigger] no[i]) == no[i + 1] by {
                if i < p {
                    assert(no[i] == oo[i] && no[i + 1] == oo[i + 1]);
                    assert(oo[i] != node as int && oo[i] != new_id);
                    assert(oo[i + 1] != new_id);
                    assert(self.data@[oo[i]] == old(self).data@[oo[i]]);
                    assert(old(self).snext(oo[i]) == oo[i + 1]);
                } else if i == p {
                    assert(no[i] == node as int && no[i + 1] == new_id);
                } else if i == p + 1 {
                    assert(no[i] == new_id && no[i + 1] == oo[p + 1]);
                } else {
                    // i >= p + 2
                    assert(no[i] == oo[i - 1] && no[i + 1] == oo[i]);
                    assert(oo[i - 1] != node as int);
                    assert(oo[i - 1] != new_id);
                    assert(self.data@[oo[i - 1]]->Some_0.next == old(self).data@[oo[i - 1]]->Some_0.next);
                    assert(old(self).snext(oo[i - 1]) == oo[i]);
                }
            }
            // (g)/(f) last node has null next
            if !is_last {
                assert(no[L] == oo[L - 1]);
                assert(oo[L - 1] != node as int);
                assert(self.data@[oo[L - 1]]->Some_0.next == old(self).data@[oo[L - 1]]->Some_0.next);
                assert(old(self).snext(oo[L - 1]) == null() as int);
            }
            // (h) backward links
            assert forall|i: int| 1 <= i < no.len() implies self.sprec(#[trigger] no[i]) == no[i - 1] by {
                if i <= p {
                    assert(no[i] == oo[i] && no[i - 1] == oo[i - 1]);
                    assert(oo[i] != new_id);
                    assert(self.data@[oo[i]]->Some_0.prec == old(self).data@[oo[i]]->Some_0.prec);
                    assert(old(self).sprec(oo[i]) == oo[i - 1]);
                } else if i == p + 1 {
                    assert(no[i] == new_id && no[i - 1] == node as int);
                } else if i == p + 2 {
                    assert(no[i] == oo[p + 1] && no[i - 1] == new_id);
                } else {
                    // i >= p + 3
                    assert(no[i] == oo[i - 1] && no[i - 1] == oo[i - 2]);
                    assert(oo[i - 1] != node as int && oo[i - 1] != new_id);
                    assert(self.data@[oo[i - 1]]->Some_0.prec == old(self).data@[oo[i - 1]]->Some_0.prec);
                    assert(old(self).sprec(oo[i - 1]) == oo[i - 2]);
                }
            }
            // free_list untouched
            assert forall|j: int| 0 <= j < self.free_list.len() implies {
                let f = #[trigger] self.free_list@[j] as int;
                0 <= f < self.data.len() && self.data@[f] is None
            } by {
                let f = self.free_list@[j] as int;
                assert(f != new_id);
                assert(self.data@[f] == s1.data@[f]);
            }

            assert(0 <= p < oo.len() && oo[p] == node as int
                && self.order@ == oo.insert(p + 1, new_node as int));
            self.lemma_inv_valid();
        }
        new_node
    }

    /// Insert `value` immediately before the live node `node`.
    ///
    /// As with `insert_after`, the original empty / `u32::MAX` guards are elided
    /// because the precondition `slive(node)` rules them out.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(100)]
    pub fn insert_before(&mut self, node: u32, value: T) -> (r: u32)
        requires
            old(self).inv(),
            old(self).slive(node as int),
            old(self).data.len() < u32::MAX as int - 1,
        ensures
            final(self).inv(),
            final(self).valid_chain(),
            r != null(),
            final(self).slive(r as int),
            final(self).sval(r as int) == value,
            !old(self).order@.contains(r as int),
            final(self).snext(r as int) == node,           // next(new) = node
            final(self).sprec(node as int) == r as int,    // prec(node) = new
            exists|p: int|
                #![auto]
                0 <= p < old(self).order@.len() && old(self).order@[p] == node as int
                    && final(self).order@ == old(self).order@.insert(p, r as int),
    {
        let ghost oo = self.order@;
        let ghost L: int = oo.len() as int;
        proof {
            assert(self.order@.contains(node as int));
        }
        let new_node = self.allocate(value);
        let ghost s1 = *self;
        proof {
            assert(self.data@[node as int] == old(self).data@[node as int]);
            assert((node as int) < self.data.len());
        }
        let cnode_prec = self.data[node as usize].as_ref().unwrap().prec;
        proof {
            assert(cnode_prec == old(self).data@[node as int]->Some_0.prec);
            assert(node as int != new_node as int);
            assert((new_node as int) < self.data.len());
        }
        self.link(new_node, node);
        let ghost s2 = *self;
        proof {
            assert(self.data@[new_node as int] is Some);
            if (cnode_prec as int) < self.data.len() {
                assert(self.data@[cnode_prec as int] == old(self).data@[cnode_prec as int]);
                assert(new_node as int != cnode_prec as int);
            }
        }
        self.link(cnode_prec, new_node);
        let ghost s3 = *self;
        if node == self.first {
            self.first = new_node;
        }
        proof {
            let ghost p = choose|q: int| 0 <= q < oo.len() && oo[q] == node as int;
            assert(0 <= p < L && oo[p] == node as int);
            self.order@ = oo.insert(p, new_node as int);
            let no = self.order@;
            let ghost new_id = new_node as int;

            assert(no.len() == L + 1);
            assert(no[p] == new_id);
            assert(forall|i: int| 0 <= i < p ==> no[i] == oo[i]);
            assert(forall|i: int| p < i <= L ==> no[i] == oo[i - 1]);
            assert(forall|j: int| 0 <= j < L ==> oo[j] != new_id);

            // Field values of the three touched slots.
            assert(self.snext(new_id) == node as int);     // link1
            assert(self.sprec(node as int) == new_id);      // link1
            assert(self.data@[new_id]->Some_0.prec == cnode_prec);  // link2
            let ghost is_first = (p == 0);
            if p > 0 {
                assert(old(self).sprec(oo[p]) == oo[p - 1]);   // old back link
                assert((cnode_prec as int) == oo[p - 1]);
                assert(self.slive(oo[p - 1]));
                assert(self.snext(oo[p - 1]) == new_id);        // link2 set next
                assert(self.first == old(self).first);
            } else {
                assert(old(self).sprec(oo[p]) == null() as int);  // node was first
                assert(cnode_prec == null());
                assert(self.sprec(new_id) == null() as int);
                assert(self.first == new_node);
            }

            // (b) liveness
            assert forall|i: int| 0 <= i < no.len() implies self.slive(#[trigger] no[i]) by {
                if i == p {
                } else if i < p {
                    assert(no[i] == oo[i]);
                    assert(old(self).slive(oo[i]));
                    assert(self.data@[oo[i]] is Some);
                } else {
                    assert(no[i] == oo[i - 1]);
                    assert(old(self).slive(oo[i - 1]));
                    assert(self.data@[oo[i - 1]] is Some);
                }
            }
            // (c) every live node is in order
            assert forall|i: int| self.slive(i) implies #[trigger] no.contains(i) by {
                if i != new_id {
                    if 0 <= i < old(self).data.len() {
                        assert(self.data@[i] is Some ==> old(self).data@[i] is Some);
                        assert(old(self).slive(i));
                        assert(old(self).order@.contains(i));
                        let k = choose|k: int| 0 <= k < oo.len() && oo[k] == i;
                        if k < p {
                            assert(no[k] == i);
                        } else {
                            assert(no[k + 1] == i);
                        }
                    } else {
                        assert(!self.slive(i));
                    }
                } else {
                    assert(no[p] == i);
                }
            }
            // (d) distinctness
            assert forall|k1: int, k2: int|
                0 <= k1 < no.len() && 0 <= k2 < no.len() && no[k1] == no[k2] implies k1 == k2 by {
                lemma_insert_distinct(oo, p, new_id, k1, k2);
            }
            // (f) forward links
            assert forall|i: int| 0 <= i < no.len() - 1 implies self.snext(#[trigger] no[i]) == no[i + 1] by {
                if i < p - 1 {
                    assert(no[i] == oo[i] && no[i + 1] == oo[i + 1]);
                    assert(oo[i] != node as int && oo[i] != new_id);
                    assert(self.data@[oo[i]]->Some_0.next == old(self).data@[oo[i]]->Some_0.next);
                    assert(old(self).snext(oo[i]) == oo[i + 1]);
                } else if i == p - 1 {
                    assert(no[i] == oo[p - 1] && no[i + 1] == new_id);
                } else if i == p {
                    assert(no[i] == new_id && no[i + 1] == node as int);
                } else {
                    // i >= p + 1
                    assert(no[i] == oo[i - 1] && no[i + 1] == oo[i]);
                    assert(oo[i - 1] != new_id);
                    assert(self.data@[oo[i - 1]]->Some_0.next == old(self).data@[oo[i - 1]]->Some_0.next);
                    assert(old(self).snext(oo[i - 1]) == oo[i]);
                }
            }
            // last node still has null next
            assert(no[L] == oo[L - 1]);
            assert(oo[L - 1] != new_id);
            assert(self.data@[oo[L - 1]]->Some_0.next == old(self).data@[oo[L - 1]]->Some_0.next);
            assert(old(self).snext(oo[L - 1]) == null() as int);
            // (h) backward links
            assert forall|i: int| 1 <= i < no.len() implies self.sprec(#[trigger] no[i]) == no[i - 1] by {
                if i < p {
                    assert(no[i] == oo[i] && no[i - 1] == oo[i - 1]);
                    assert(oo[i] != node as int && oo[i] != new_id);
                    assert(self.data@[oo[i]]->Some_0.prec == old(self).data@[oo[i]]->Some_0.prec);
                    assert(old(self).sprec(oo[i]) == oo[i - 1]);
                } else if i == p {
                    assert(no[i] == new_id && no[i - 1] == oo[p - 1]);
                } else if i == p + 1 {
                    assert(no[i] == node as int && no[i - 1] == new_id);
                } else {
                    // i >= p + 2
                    assert(no[i] == oo[i - 1] && no[i - 1] == oo[i - 2]);
                    assert(oo[i - 1] != node as int && oo[i - 1] != new_id);
                    assert(self.data@[oo[i - 1]]->Some_0.prec == old(self).data@[oo[i - 1]]->Some_0.prec);
                    assert(old(self).sprec(oo[i - 1]) == oo[i - 2]);
                }
            }
            // first node still has null prec
            assert(no[0] == oo[0] || no[0] == new_id);
            // free_list untouched
            assert forall|j: int| 0 <= j < self.free_list.len() implies {
                let f = #[trigger] self.free_list@[j] as int;
                0 <= f < self.data.len() && self.data@[f] is None
            } by {
                let f = self.free_list@[j] as int;
                assert(f != new_id);
                assert(self.data@[f] == s1.data@[f]);
            }

            assert(0 <= p < oo.len() && oo[p] == node as int
                && self.order@ == oo.insert(p, new_node as int));
            self.lemma_inv_valid();
        }
        new_node
    }

    /// Remove the live node `node` from the list.
    ///
    /// The original `unsafe` marker and the `node >= len` / dead-node `panic`
    /// guards are elided: the precondition `slive(node)` makes them unreachable.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(250)]
    pub fn delete(&mut self, node: u32)
        requires
            old(self).inv(),
            old(self).slive(node as int),
        ensures
            final(self).inv(),
            final(self).valid_chain(),
            !final(self).slive(node as int),
            final(self).order@.len() == old(self).order@.len() - 1,
            exists|p: int|
                #![auto]
                0 <= p < old(self).order@.len() && old(self).order@[p] == node as int
                    && final(self).order@ == old(self).order@.remove(p),
    {
        let ghost oo = self.order@;
        let ghost L: int = oo.len() as int;
        proof {
            assert(self.order@.contains(node as int));
            assert((node as int) < self.data.len());
        }
        let node_prec = self.data[node as usize].as_ref().unwrap().prec;
        let node_next = self.data[node as usize].as_ref().unwrap().next;
        let ghost p = choose|q: int| 0 <= q < oo.len() && oo[q] == node as int;
        proof {
            assert(0 <= p < L && oo[p] == node as int);
            assert(node_prec == old(self).data@[node as int]->Some_0.prec);
            assert(node_next == old(self).data@[node as int]->Some_0.next);
            if p > 0 {
                assert(old(self).sprec(oo[p]) == oo[p - 1]);
                assert(node_prec as int == oo[p - 1]);
                assert(self.slive(oo[p - 1]));
            } else {
                assert(old(self).sprec(oo[p]) == null() as int);
                assert(node_prec == null());
            }
            if p < L - 1 {
                assert(old(self).snext(oo[p]) == oo[p + 1]);
                assert(node_next as int == oo[p + 1]);
                assert(self.slive(oo[p + 1]));
            } else {
                assert(old(self).snext(oo[p]) == null() as int);
                assert(node_next == null());
            }
            // link preconditions: prec/next live (or out of range) and distinct
            if (node_prec as int) < self.data.len() && (node_next as int) < self.data.len() {
                assert(node_prec != node_next);  // oo[p-1] != oo[p+1]
            }
        }
        self.link(node_prec, node_next);
        let ghost s1 = *self;
        if node == self.first {
            self.first = node_next;
        }
        if node == self.last {
            self.last = node_prec;
        }
        self.data.set(node as usize, None);
        self.free_list.push(node);
        proof {
            self.order@ = oo.remove(p);
            let no = self.order@;
            assert(no.len() == L - 1);
            assert(forall|i: int| 0 <= i < p ==> no[i] == oo[i]);
            assert(forall|i: int| p <= i < L - 1 ==> no[i] == oo[i + 1]);

            // touched-slot field values
            assert(self.data@[node as int] is None);          // set
            if p > 0 {
                assert(self.snext(node_prec as int) == node_next as int);  // link
                assert(node_prec as int == oo[p - 1]);
            }
            if p < L - 1 {
                assert(self.sprec(node_next as int) == node_prec as int);  // link
                assert(node_next as int == oo[p + 1]);
            }
            // endpoints
            if p == 0 {
                assert(self.first == node_next);
            } else {
                assert(self.first == old(self).first);
            }
            if p == L - 1 {
                assert(self.last == node_prec);
            } else {
                assert(self.last == old(self).last);
            }

            // (b) liveness of every remaining order entry
            assert forall|i: int| 0 <= i < no.len() implies self.slive(#[trigger] no[i]) by {
                let src = if i < p { i } else { i + 1 };
                assert(no[i] == oo[src]);
                assert(old(self).slive(oo[src]));
                assert(oo[src] != node as int);    // src != p (distinctness)
                assert(self.data@[oo[src]] is Some);
            }
            // (c) every live node is in order
            assert forall|i: int| self.slive(i) implies #[trigger] no.contains(i) by {
                assert(i != node as int);          // node is now dead
                assert(self.data@[i] is Some ==> old(self).data@[i] is Some);
                assert(old(self).slive(i));
                assert(old(self).order@.contains(i));
                let k = choose|k: int| 0 <= k < oo.len() && oo[k] == i;
                assert(k != p);                    // oo[p] == node != i
                if k < p {
                    assert(no[k] == i);
                } else {
                    assert(no[k - 1] == i);
                }
            }
            // (d) distinctness
            assert forall|k1: int, k2: int|
                0 <= k1 < no.len() && 0 <= k2 < no.len() && no[k1] == no[k2] implies k1 == k2 by {
                lemma_remove_distinct(oo, p, k1, k2);
            }
            // The `next` field is mutated only at `node_prec` (and at `node`,
            // now dead); the `prec` field only at `node_next` (and `node`).
            // (f) forward links
            assert forall|i: int| 0 <= i < no.len() - 1 implies self.snext(#[trigger] no[i]) == no[i + 1] by {
                if i < p - 1 {
                    assert(no[i] == oo[i] && no[i + 1] == oo[i + 1]);
                    assert(oo[i] != node as int && oo[i] != node_prec as int);
                    assert(self.data@[oo[i]]->Some_0.next == old(self).data@[oo[i]]->Some_0.next);
                    assert(old(self).snext(oo[i]) == oo[i + 1]);
                } else if i == p - 1 {
                    assert(no[i] == oo[p - 1] && no[i + 1] == oo[p + 1]);
                } else {
                    // i >= p
                    assert(no[i] == oo[i + 1] && no[i + 1] == oo[i + 2]);
                    assert(oo[i + 1] != node as int && oo[i + 1] != node_prec as int);
                    assert(self.data@[oo[i + 1]]->Some_0.next == old(self).data@[oo[i + 1]]->Some_0.next);
                    assert(old(self).snext(oo[i + 1]) == oo[i + 2]);
                }
            }
            // last node has null next
            if no.len() > 0 {
                let last_src = if L - 2 < p { L - 2 } else { L - 1 };
                assert(no[L - 2] == oo[last_src]);
                assert(oo[last_src] != node as int);
                if p == L - 1 {
                    // node was last; node_prec is the new last with next = null
                    assert(oo[last_src] == node_prec as int);
                    assert(self.snext(node_prec as int) == null() as int);
                } else {
                    assert(oo[last_src] != node_prec as int);
                    assert(self.data@[oo[last_src]]->Some_0.next == old(self).data@[oo[last_src]]->Some_0.next);
                    assert(old(self).snext(oo[last_src]) == null() as int);
                }
            }
            // (h) backward links
            assert forall|i: int| 1 <= i < no.len() implies self.sprec(#[trigger] no[i]) == no[i - 1] by {
                if i < p {
                    assert(no[i] == oo[i] && no[i - 1] == oo[i - 1]);
                    assert(oo[i] != node as int && oo[i] != node_next as int);
                    assert(self.data@[oo[i]]->Some_0.prec == old(self).data@[oo[i]]->Some_0.prec);
                    assert(old(self).sprec(oo[i]) == oo[i - 1]);
                } else if i == p {
                    assert(no[i] == oo[p + 1] && no[i - 1] == oo[p - 1]);
                } else {
                    // i >= p + 1
                    assert(no[i] == oo[i + 1] && no[i - 1] == oo[i]);
                    assert(oo[i + 1] != node as int && oo[i + 1] != node_next as int);
                    assert(self.data@[oo[i + 1]]->Some_0.prec == old(self).data@[oo[i + 1]]->Some_0.prec);
                    assert(old(self).sprec(oo[i + 1]) == oo[i]);
                }
            }
            // first node has null prec
            if no.len() > 0 {
                let first_src = if 0 < p { 0 } else { 1 };
                assert(no[0] == oo[first_src]);
                assert(oo[first_src] != node as int);
                if p == 0 {
                    assert(oo[first_src] == node_next as int);
                    assert(self.sprec(node_next as int) == null() as int);
                } else {
                    assert(oo[first_src] != node_next as int);
                    assert(self.data@[oo[first_src]]->Some_0.prec == old(self).data@[oo[first_src]]->Some_0.prec);
                    assert(old(self).sprec(oo[first_src]) == null() as int);
                }
            }
            // free_list: old entries still dead + node is freshly freed, all distinct
            assert(self.free_list@ == old(self).free_list@.push(node));
            assert forall|j: int| 0 <= j < self.free_list.len() implies {
                let f = #[trigger] self.free_list@[j] as int;
                0 <= f < self.data.len() && self.data@[f] is None
            } by {
                if j < old(self).free_list.len() {
                    assert(self.free_list@[j] == old(self).free_list@[j]);
                    assert(old(self).data@[self.free_list@[j] as int] is None);  // old free_list dead
                    assert(self.free_list@[j] != node);     // node was live
                    assert(self.data@[self.free_list@[j] as int] == s1.data@[self.free_list@[j] as int]);
                } else {
                    assert(self.free_list@[j] == node);
                }
            }
            assert forall|j1: int, j2: int|
                0 <= j1 < self.free_list.len() && 0 <= j2 < self.free_list.len()
                    && self.free_list@[j1] == self.free_list@[j2] implies j1 == j2 by {
                // node is not among the old (dead) entries, so the push stays distinct
                assert(old(self).data@[node as int] is Some);
            }

            assert(0 <= p < oo.len() && oo[p] == node as int && self.order@ == oo.remove(p));
            self.lemma_inv_valid();
        }
    }
}

fn main() {}

} // verus!
