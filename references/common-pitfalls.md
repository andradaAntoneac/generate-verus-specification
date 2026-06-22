# Common Pitfalls

## Using `int` in exec code
Example:
```
fn add_one(x: int) -> int { x + 1 }
```
Fix: use machine integers in exec code and reserve `int` for spec/proof.
```
fn add_one(x: u32) -> u32 { x + 1 }
```

## Missing `decreases` on recursion
Example:
```
spec fn len_rec(n: nat) -> nat {
    if n == 0 { 0 } else { 1 + len_rec(n - 1) }
}
```
Fix: add a termination metric.
```
spec fn len_rec(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { 1 + len_rec(n - 1) }
}
```

## Quantifier not triggering
Example:
```
assert(forall |i: int| s.contains(i) ==> s.contains(i));
```
Fix: add a trigger to the membership test.
```
assert(forall |i: int| #[trigger] s.contains(i) ==> s.contains(i));
```

## Overflow in machine integers
Example:
```
ensures result == x + 1
```
Fix: add bounds in `requires` so the arithmetic is safe.
```
requires x < u32::MAX
ensures result == x + 1
```

## Missing `old(...)` for pre-state
Example:
```
ensures self.len() == self.len() + 1
```
Fix: use `old(self)` (or `old(x)`) for pre-state values of `&mut`.
```
ensures self.len() == old(self).len() + 1
```

## Mixing storage details into the abstract spec
Example:
```
ensures data.len() == old(data).len() + 1
```
Fix: express the effect in terms of the abstract list view and node set.
```
ensures self.list_view() == old(self).list_view() + seq![value]
```

## Missing bidirectional link consistency
Example:
```
ensures self.next(id) == Some(id_next)
```
Fix: also assert the corresponding predecessor relation.
```
ensures self.next(id) == Some(id_next)
ensures self.prev(id_next) == Some(id)
```


Fix: add reachability facts (from `first` and to `last`) to pin down the chain.
```
ensures self.wf_list()
ensures forall |id: NodeId| self.nodes().contains(id)
        ==> self.reachable_from_first(id)
ensures forall |id: NodeId| self.nodes().contains(id)
        ==> self.reachable_to_last(id)
```