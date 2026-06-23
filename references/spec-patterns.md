# Specification Patterns

## Pattern: Bounded value
requires 0 <= x < N

## Pattern: Collection length consistency
ensures result.len() == old(v).len()

## Pattern: Sortedness
spec fn sorted(s: Seq<int>) -> bool {
    forall|i:int, j:int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

## Pattern: Algebraic law (commutativity)
proof fn commutes(a: int, b: int)
    ensures f(a,b) == f(b,a)

## Pattern: Algebraic law (identity)
proof fn identity(a: int)
    ensures 
        f(a, e) == a,
        f(e, a) == a

## Pattern: Algebraic law (associativity)
proof fn associativity(a: int, b: int, c: int)
    ensures f(f(a, b), c) == f(a, f(b, c))

## Pattern: Algebraic law (idempotence)
proof fn idempotence(a: int)
    ensures f(a, a) == a

## Pattern: Algebraic law (monotonicity)
proof fn monotone(a: int, b: int)
    requires a <= b
    ensures f(a) <= f(b)

## Pattern: Algebraic law (distributivity)
proof fn distributes(a: int, b: int, c: int)
    ensures f(a, g(b, c)) == g(f(a, b), f(a, c))

## Pattern: Abstract DLL state (storage-agnostic)
Define the abstract view of the list independently of the backing storage.
```
spec fn nodes(self) -> Set<NodeId>
spec fn first(self) -> Option<NodeId>
spec fn last(self) -> Option<NodeId>
spec fn next(self, id: NodeId) -> Option<NodeId>
spec fn prev(self, id: NodeId) -> Option<NodeId>
spec fn value(self, id: NodeId) -> T
```

## Pattern: Abstract DLL well-formedness
```
spec fn wf_list(self) -> bool {
    &&& (self.nodes().is_empty() <==> self.first().is_none())
    &&& (self.nodes().is_empty() <==> self.last().is_none())
    &&& self.first().is_some() ==> self.nodes().contains(self.first().unwrap())
    &&& self.last().is_some() ==> self.nodes().contains(self.last().unwrap())
    &&& forall |id: NodeId| self.nodes().contains(id) ==> {
        let n = self.next(id);
        let p = self.prev(id);
        &&& n.is_some() ==> self.nodes().contains(n.unwrap())
        &&& p.is_some() ==> self.nodes().contains(p.unwrap())
        &&& n.is_some() ==> self.prev(n.unwrap()) == Some(id)
        &&& p.is_some() ==> self.next(p.unwrap()) == Some(id)
    }
    &&& self.first().is_some() ==> self.prev(self.first().unwrap()).is_none()
    &&& self.last().is_some() ==> self.next(self.last().unwrap()).is_none()
}
```

## Pattern: List view (sequence abstraction)
```
spec fn list_view(self) -> Seq<T> { /* traverse from first via next */ }
```

## Pattern: Link update postconditions (frame)
Use for mutating operations that change a few links. Mirror the concrete code
path and record which keys changed, with a frame for all others.
```
ensures 
    self.next(a) == Some(b),
    self.prev(b) == Some(a),
    forall |id: NodeId|
        id != a && id != b ==> {
        self.next(id) == old(self).next(id)
        && self.prev(id) == old(self).prev(id)
    },
```
Extend with explicit `first`/`last` updates when those fields change.

## Pattern: Value tracking with `View`
Use when operations take `value: T` and the spec must track values explicitly.
Require `T: View` and store a ghost sequence.
```
struct Dll<T: View> {
    // concrete fields ...
    ghost values: Ghost<Seq<T>>,
}
```
Push postconditions update the ghost sequence:
```
ensures self.values@ == old(self).values@ + seq![value]   // push_back
ensures self.values@ == seq![value] + old(self).values@   // push_front
```

## Pattern: List view updates
- Push back:
  `ensures self.list_view() == old(self).list_view() + seq![value]`
- Push front:
  `ensures self.list_view() == seq![value] + old(self).list_view()`
- Insert before/after:
  `ensures self.list_view() == prefix + seq![value] + suffix`
- Delete:
  `ensures self.list_view() == old(self).list_view().remove(idx)`