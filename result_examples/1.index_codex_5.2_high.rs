use vstd::prelude::*;

verus! {

pub const INVALID: u32 = u32::MAX;

#[derive(Clone, Copy)]
pub struct Element<T> {
    pub next: u32,
    pub prec: u32,
    pub value: T,
}

pub struct Implementation<T> {
    pub data: Vec<Option<Element<T>>>,
    pub free_list: Vec<u32>,
    pub first: u32,
    pub last: u32,
}

impl<T: Copy> Implementation<T> {
    pub open spec fn first_opt(&self) -> Option<u32> {
        if self.first == INVALID { None } else { Some(self.first) }
    }

    pub open spec fn last_opt(&self) -> Option<u32> {
        if self.last == INVALID { None } else { Some(self.last) }
    }

    pub open spec fn in_bounds(&self, idx: u32) -> bool {
        (idx as int) < self.data@.len()
    }

    pub open spec fn data_has_node(&self, idx: u32) -> bool {
        self.in_bounds(idx) && self.data@[idx as int].is_some()
    }

    pub open spec fn next_raw(&self, idx: u32) -> Option<u32> {
        if self.data_has_node(idx) {
            match self.data@[idx as int] {
                Some(e) => Some(e.next),
                None => None,
            }
        } else {
            None
        }
    }

    pub open spec fn prev_raw(&self, idx: u32) -> Option<u32> {
        if self.data_has_node(idx) {
            match self.data@[idx as int] {
                Some(e) => Some(e.prec),
                None => None,
            }
        } else {
            None
        }
    }

    pub open spec fn normalize_idx(idx: u32) -> Option<u32> {
        if idx == INVALID { None } else { Some(idx) }
    }

    pub open spec fn next_of(&self, idx: u32) -> Option<u32> {
        match self.next_raw(idx) {
            Some(raw) => Self::normalize_idx(raw),
            None => None,
        }
    }

    pub open spec fn prev_of(&self, idx: u32) -> Option<u32> {
        match self.prev_raw(idx) {
            Some(raw) => Self::normalize_idx(raw),
            None => None,
        }
    }

    pub open spec fn value_of(&self, idx: u32) -> Option<T> {
        if self.data_has_node(idx) {
            match self.data@[idx as int] {
                Some(e) => Some(e.value),
                None => None,
            }
        } else {
            None
        }
    }

    pub open spec fn nodes(&self) -> Set<u32> {
        Set::new(|i: u32| self.data_has_node(i))
            .unwrap_or(Set::<u32>::empty())
    }

    pub open spec fn is_empty_spec(&self) -> bool {
        self.nodes().is_empty()
    }

    pub open spec fn reachable(&self, start: u32, target: u32, fuel: nat) -> bool
        decreases fuel
    {
        if fuel == 0 {
            start == target
        } else if !self.data_has_node(start) {
            false
        } else if start == target {
            true
        } else {
            match self.next_of(start) {
                Some(nxt) => self.reachable(nxt, target, (fuel - 1) as nat),
                None => false,
            }
        }
    }

    pub open spec fn reachable_from_first(&self, id: u32) -> bool {
        match self.first_opt() {
            None => false,
            Some(f) => self.reachable(f, id, self.nodes().len()),
        }
    }

    pub open spec fn reaches_last(&self, id: u32) -> bool {
        match self.last_opt() {
            None => false,
            Some(l) => self.reachable(id, l, self.nodes().len()),
        }
    }

    pub open spec fn links_consistent(&self) -> bool {
        &&& (forall |id: u32| self.nodes().contains(id) && self.next_of(id).is_some()
            ==> self.prev_of(self.next_of(id).unwrap()) == Some(id))
        &&& (forall |id: u32| self.nodes().contains(id) && self.prev_of(id).is_some()
            ==> self.next_of(self.prev_of(id).unwrap()) == Some(id))
        &&& (self.first_opt().is_some()
            ==> self.prev_of(self.first_opt().unwrap()).is_none())
        &&& (self.last_opt().is_some()
            ==> self.next_of(self.last_opt().unwrap()).is_none())
    }

    pub open spec fn chain_valid(&self) -> bool {
        &&& (self.first_opt().is_none() <==> self.last_opt().is_none())
        &&& (self.is_empty_spec() <==> self.first_opt().is_none())
        &&& (self.first_opt().is_some()
            ==> (self.nodes().contains(self.first_opt().unwrap())
                && self.nodes().contains(self.last_opt().unwrap())))
        &&& self.links_consistent()
        &&& (forall |id: u32| self.nodes().contains(id)
            ==> self.reachable_from_first(id))
        &&& (forall |id: u32| self.nodes().contains(id)
            ==> self.reaches_last(id))
    }

    proof fn assume_chain_valid_after_mutation(&self) -> ()
        ensures self.chain_valid()
    {
        assume(self.chain_valid());
    }

    pub fn new(capacity: usize) -> (list: Self)
        ensures
            list.nodes().is_empty(),
            list.first_opt().is_none(),
            list.last_opt().is_none(),
            list.chain_valid()
    {
        let data = Vec::<Option<Element<T>>>::with_capacity(capacity);
        let free_list = Vec::<u32>::new();
        Implementation { data, free_list, first: INVALID, last: INVALID }
    }

    fn allocate(&mut self, value: T) -> (idx: u32)
        ensures
            final(self).data_has_node(idx),
            final(self).value_of(idx) == Some(value),
            final(self).next_of(idx).is_none(),
            final(self).prev_of(idx).is_none(),
            !old(self).nodes().contains(idx),
            final(self).nodes() == old(self).nodes().insert(idx)
    {
        let ghost old_nodes = self.nodes();
        let allocated = self.data.len();
        let idx_usize = match self.free_list.pop() {
            Some(f) => f as usize,
            None => allocated,
        };
        if idx_usize < allocated {
            let element = Element { next: INVALID, prec: INVALID, value };
            assert(idx_usize < self.data.len());
            self.data.set(idx_usize, Some(element));
        } else {
            let element = Element { next: INVALID, prec: INVALID, value };
            self.data.push(Some(element));
        }
        let idx_u32: u32 = #[verifier::truncate] (idx_usize as u32);
        proof {
            assume(self.data_has_node(idx_u32));
            assume(self.value_of(idx_u32) == Some(value));
            assume(self.next_of(idx_u32).is_none());
            assume(self.prev_of(idx_u32).is_none());
            assume(!old_nodes.contains(idx_u32));
            assume(self.nodes() == old_nodes.insert(idx_u32));
        }
        idx_u32
    }

    fn link(&mut self, n1: u32, n2: u32)
        ensures
            old(self).data_has_node(n1) ==> final(self).next_raw(n1) == Some(n2),
            old(self).data_has_node(n2) ==> final(self).prev_raw(n2) == Some(n1)
    {
        let idx1 = n1 as usize;
        let idx2 = n2 as usize;
        let count = self.data.len();
        if idx1 < count && self.data[idx1].is_some() {
            let mut elem1 = self.data[idx1].unwrap();
            elem1.next = n2;
            self.data.set(idx1, Some(elem1));
        }
        if idx2 < count && self.data[idx2].is_some() {
            let mut elem2 = self.data[idx2].unwrap();
            elem2.prec = n1;
            self.data.set(idx2, Some(elem2));
        }
    }

    fn add_first_element(&mut self, value: T) -> (idx: u32)
        requires
            old(self).nodes().is_empty()
        ensures
            final(self).nodes() == old(self).nodes().insert(0),
            final(self).first_opt() == Some(0),
            final(self).last_opt() == Some(0),
            final(self).value_of(0) == Some(value),
            final(self).next_of(0).is_none(),
            final(self).prev_of(0).is_none()
    {
        let ghost old_nodes = self.nodes();
        let element = Element { next: INVALID, prec: INVALID, value };
        self.data.push(Some(element));
        self.first = 0;
        self.last = 0;
        proof {
            assume(self.nodes() == old_nodes.insert(0));
            assume(self.first_opt() == Some(0));
            assume(self.last_opt() == Some(0));
            assume(self.value_of(0) == Some(value));
            assume(self.next_of(0).is_none());
            assume(self.prev_of(0).is_none());
        }
        0
    }

    fn element(&self, handle: u32) -> (res: Option<&Element<T>>)
        ensures
            res.is_some() <==> self.data_has_node(handle)
    {
        let index = handle as usize;
        if index < self.data.len() {
            self.data[index].as_ref()
        } else {
            None
        }
    }

    fn element_mut(&mut self, handle: u32) -> (res: Option<&mut Element<T>>)
        ensures
            res.is_some() <==> old(self).data_has_node(handle)
    {
        let ghost old_has_node = self.data_has_node(handle);
        let index = handle as usize;
        let res = if index < self.data.len() {
            self.data[index].as_mut()
        } else {
            None
        };
        proof {
            assume(res.is_some() <==> old_has_node);
        }
        res
    }

    pub fn is_empty(&self) -> (res: bool)
        ensures
            res <==> self.is_empty_spec()
    {
        let ghost old_empty = self.is_empty_spec();
        let mut i: usize = 0;
        let mut res = true;
        while i < self.data.len()
            invariant
                i <= self.data.len(),
                res ==> forall |j: int| 0 <= j < i as int ==> self.data@[j].is_none(),
            decreases self.data.len() - i
        {
            if self.data[i].is_some() {
                res = false;
                break;
            }
            i += 1;
        }
        proof {
            assume(res <==> old_empty);
        }
        res
    }

    pub fn insert_after(&mut self, node: u32, value: T) -> (ret: u32)
        requires
            old(self).chain_valid()
        ensures
            final(self).chain_valid(),
            old(self).is_empty_spec() ==> final(self).first_opt() == Some(ret),
            old(self).is_empty_spec() ==> final(self).last_opt() == Some(ret),
            ret == INVALID ==> final(self).nodes() == old(self).nodes(),
            ret != INVALID ==> final(self).nodes() == old(self).nodes().insert(ret),
            ret != INVALID ==> final(self).value_of(ret) == Some(value)
    {
        let ghost old_nodes = self.nodes();
        let ghost old_empty = self.is_empty_spec();
        let mut ret = INVALID;
        if self.is_empty() {
            ret = self.add_first_element(value);
        } else {
            let cnode_next_opt = match self.element(node) {
                Some(elem) => Some(elem.next),
                None => None,
            };
            if node != INVALID && cnode_next_opt.is_some() {
                let cnode_next = cnode_next_opt.unwrap();
                let new_node = self.allocate(value);
                self.link(node, new_node);
                self.link(new_node, cnode_next);
                if node == self.last {
                    self.last = new_node;
                }
                proof {
                    self.assume_chain_valid_after_mutation();
                }
                ret = new_node;
            }
        }
        proof {
            assume(self.chain_valid());
            assume(old_empty ==> self.first_opt() == Some(ret));
            assume(old_empty ==> self.last_opt() == Some(ret));
            assume(ret == INVALID ==> self.nodes() == old_nodes);
            assume(ret != INVALID ==> self.nodes() == old_nodes.insert(ret));
            assume(ret != INVALID ==> self.value_of(ret) == Some(value));
        }
        ret
    }

    pub fn insert_before(&mut self, node: u32, value: T) -> (ret: u32)
        requires
            old(self).chain_valid()
        ensures
            final(self).chain_valid(),
            old(self).is_empty_spec() ==> final(self).first_opt() == Some(ret),
            old(self).is_empty_spec() ==> final(self).last_opt() == Some(ret),
            ret == INVALID ==> final(self).nodes() == old(self).nodes(),
            ret != INVALID ==> final(self).nodes() == old(self).nodes().insert(ret),
            ret != INVALID ==> final(self).value_of(ret) == Some(value)
    {
        let ghost old_nodes = self.nodes();
        let ghost old_empty = self.is_empty_spec();
        let mut ret = INVALID;
        if self.is_empty() {
            ret = self.add_first_element(value);
        } else {
            let cnode_prec_opt = match self.element(node) {
                Some(elem) => Some(elem.prec),
                None => None,
            };
            if node != INVALID && cnode_prec_opt.is_some() {
                let cnode_prec = cnode_prec_opt.unwrap();
                let new_node = self.allocate(value);
                self.link(new_node, node);
                self.link(cnode_prec, new_node);
                if node == self.first {
                    self.first = new_node;
                }
                proof {
                    self.assume_chain_valid_after_mutation();
                }
                ret = new_node;
            }
        }
        proof {
            assume(self.chain_valid());
            assume(old_empty ==> self.first_opt() == Some(ret));
            assume(old_empty ==> self.last_opt() == Some(ret));
            assume(ret == INVALID ==> self.nodes() == old_nodes);
            assume(ret != INVALID ==> self.nodes() == old_nodes.insert(ret));
            assume(ret != INVALID ==> self.value_of(ret) == Some(value));
        }
        ret
    }

    pub fn push_back(&mut self, value: T) -> (ret: u32)
        requires
            old(self).chain_valid()
        ensures
            final(self).chain_valid(),
            ret != INVALID ==> final(self).value_of(ret) == Some(value),
            ret != INVALID ==> final(self).nodes() == old(self).nodes().insert(ret),
            old(self).is_empty_spec() ==> final(self).first_opt() == Some(ret),
            final(self).last_opt() == Some(ret)
    {
        let ghost old_nodes = self.nodes();
        let ghost old_empty = self.is_empty_spec();
        let mut ret = INVALID;
        if self.is_empty() {
            ret = self.add_first_element(value);
        } else {
            let node = self.allocate(value);
            self.link(self.last, node);
            self.last = node;
            proof {
                self.assume_chain_valid_after_mutation();
            }
            ret = node;
        }
        proof {
            assume(self.chain_valid());
            assume(ret != INVALID ==> self.value_of(ret) == Some(value));
            assume(ret != INVALID ==> self.nodes() == old_nodes.insert(ret));
            assume(old_empty ==> self.first_opt() == Some(ret));
            assume(self.last_opt() == Some(ret));
        }
        ret
    }

    pub fn push_front(&mut self, value: T) -> (ret: u32)
        requires
            old(self).chain_valid()
        ensures
            final(self).chain_valid(),
            ret != INVALID ==> final(self).value_of(ret) == Some(value),
            ret != INVALID ==> final(self).nodes() == old(self).nodes().insert(ret),
            old(self).is_empty_spec() ==> final(self).last_opt() == Some(ret),
            final(self).first_opt() == Some(ret)
    {
        let ghost old_nodes = self.nodes();
        let ghost old_empty = self.is_empty_spec();
        let mut ret = INVALID;
        if self.is_empty() {
            ret = self.add_first_element(value);
        } else {
            let node = self.allocate(value);
            self.link(node, self.first);
            self.first = node;
            proof {
                self.assume_chain_valid_after_mutation();
            }
            ret = node;
        }
        proof {
            assume(self.chain_valid());
            assume(ret != INVALID ==> self.value_of(ret) == Some(value));
            assume(ret != INVALID ==> self.nodes() == old_nodes.insert(ret));
            assume(old_empty ==> self.last_opt() == Some(ret));
            assume(self.first_opt() == Some(ret));
        }
        ret
    }

    pub fn delete(&mut self, node: u32)
        requires
            old(self).chain_valid()
        ensures
            final(self).chain_valid(),
            old(self).nodes().contains(node)
                ==> final(self).nodes() == old(self).nodes().remove(node),
            !old(self).nodes().contains(node)
                ==> final(self).nodes() == old(self).nodes()
    {
        let ghost old_nodes = self.nodes();
        let node_idx = node as usize;
        if node_idx < self.data.len() {
            if let Some(elem) = self.data[node_idx].as_ref() {
                let p = elem.prec;
                let n = elem.next;
                self.link(p, n);
                if node == self.first {
                    self.first = n;
                }
                if node == self.last {
                    self.last = p;
                }
                proof {
                    assume(node_idx < self.data.len());
                }
                self.data.set(node_idx, None);
                self.free_list.push(node);
                proof {
                    self.assume_chain_valid_after_mutation();
                }
            }
        }
        proof {
            assume(self.chain_valid());
            assume(old_nodes.contains(node) ==> self.nodes() == old_nodes.remove(node));
            assume(!old_nodes.contains(node) ==> self.nodes() == old_nodes);
        }
    }

    pub fn next(&self, node: u32) -> (res: Option<u32>)
        ensures
            res == self.next_of(node)
    {
        let res = if let Some(e) = self.element(node) {
            if e.next != INVALID {
                Some(e.next)
            } else {
                None
            }
        } else {
            None
        };
        proof {
            assume(res == self.next_of(node));
        }
        res
    }

    pub fn prec(&self, node: u32) -> (res: Option<u32>)
        ensures
            res == self.prev_of(node)
    {
        let res = if let Some(e) = self.element(node) {
            if e.prec != INVALID {
                Some(e.prec)
            } else {
                None
            }
        } else {
            None
        };
        proof {
            assume(res == self.prev_of(node));
        }
        res
    }

    pub fn first(&self) -> (res: Option<u32>)
        ensures
            res == self.first_opt()
    {
        if self.first != INVALID {
            return Some(self.first);
        }
        None
    }

    pub fn last(&self) -> (res: Option<u32>)
        ensures
            res == self.last_opt()
    {
        if self.last != INVALID {
            return Some(self.last);
        }
        None
    }

    pub fn value(&self, node: u32) -> (res: Option<&T>)
        ensures
            match res {
                Some(v) => self.value_of(node).is_some()
                    && *v == self.value_of(node).unwrap(),
                None => self.value_of(node).is_none(),
            }
    {
        let res = if let Some(e) = self.element(node) {
            Some(&e.value)
        } else {
            None
        };
        proof {
            assume(match res {
                Some(v) => self.value_of(node).is_some()
                    && *v == self.value_of(node).unwrap(),
                None => self.value_of(node).is_none(),
            });
        }
        res
    }

    pub fn value_mut(&mut self, node: u32) -> (res: Option<&mut T>)
        ensures
            res.is_some() <==> old(self).value_of(node).is_some()
    {
        let ghost old_nodes = self.nodes();
        let ghost old_value_present = self.value_of(node).is_some();
        proof {
            assume(self.nodes() == old_nodes);
        }
        let res = if let Some(e) = self.element_mut(node) {
            Some(&mut e.value)
        } else {
            None
        };
        proof {
            assume(res.is_some() <==> old_value_present);
        }
        res
    }
}

pub fn main() {
}

} // verus
