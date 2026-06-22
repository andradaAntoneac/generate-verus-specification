# Proof Patterns

## Induction
Use recursive `proof fn` with `decreases`.

Example:
```
proof fn sum_prefix(n: nat)
    ensures sum(n) == sum(n - 1) + n
    decreases n
{
    if n == 0 {
        assert(sum(0) == 0);
    } else {
        sum_prefix((n - 1) as nat);
        assert(sum(n) == sum(n - 1) + n);
    }
}
```

## Case analysis
match / if then prove each branch.

Example:
```
proof fn alloc_cases(free_len: nat)
    ensures free_len > 0 || free_len == 0
{
    if free_len > 0 {
        assert(free_len > 0);
    } else {
        assert(free_len == 0);
    }
}
```

## Lemma application
Define reusable `proof fn lemma_...` and call it.

Example:
```
proof fn lemma_bounds(i: int, len: int)
    requires 0 <= i < len
    ensures i < len
{ }

proof fn use_bounds(i: int, len: int)
    requires 0 <= i < len
    ensures i < len
{
    lemma_bounds(i, len);
}
```

## Trigger tuning
When quantifiers don't fire, add `#[trigger]`.

Example:
```
proof fn trigger_example(s: Set<int>, x: int)
    requires s.contains(x)
    ensures s.contains(x)
{
    assert(forall |y: int| #[trigger] s.contains(y) ==> s.contains(y));
}
```

## Axiomatic lemma (external body)
Declare a lemma with an external body and no implementation.

Example:
```
#[verifier(external_body)]
proof fn lemma_ext_commutes(a: int, b: int)
    ensures f(a, b) == f(b, a)
;
```

## Reachability after link
Prove that adding one node preserves reachability for all nodes.

Example:
```
proof fn lemma_reachable_after_link(old_list: List, new_list: List, new_id: NodeId)
    requires old_list.wf_list()
    requires new_list.wf_list()
    requires new_list.nodes() == old_list.nodes().insert(new_id)
    ensures forall |id: NodeId| new_list.nodes().contains(id)
               ==> new_list.reachable(id)
{ }
```

## Frame lemma for untouched nodes
Use when only a few links are modified.

Example:
```
proof fn lemma_frame_next(old: List, new: List, untouched: Set<NodeId>)
    requires forall |id: NodeId| untouched.contains(id) ==>
                 old.next(id) == new.next(id)
    ensures forall |id: NodeId| untouched.contains(id) ==>
                 old.prev(id) == new.prev(id)
{ }
```