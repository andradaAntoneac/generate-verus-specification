# Data Structure Spec Template

```rust
// Preserve concrete fields; add ghost fields only as additions.
pub struct STRUCT_NAME<T> {
    // concrete fields...
    // ghost fields (optional), e.g.:
    // ghost values: Ghost<Seq<T>>,
}

impl STRUCT_NAME<T> {
    // Abstract view helpers (storage-agnostic).
    spec fn nodes(self) -> Set<NodeId> { /* ... */ }
    spec fn first(self) -> Option<NodeId> { /* ... */ }
    spec fn last(self) -> Option<NodeId> { /* ... */ }
    spec fn next(self, id: NodeId) -> Option<NodeId> { /* ... */ }
    spec fn prev(self, id: NodeId) -> Option<NodeId> { /* ... */ }
    spec fn value(self, id: NodeId) -> T { /* ... */ }

    // Well-formedness predicate (abstract invariant).
    spec fn wf_list(self) -> bool { /* ... */ }

    // Sequence abstraction for order-sensitive properties.
    spec fn list_view(self) -> Seq<T> { /* traverse from first via next */ }
}

// Optional: consistency lemmas for mutating operations.
// proof fn lemma_consistency_push_back(old: STRUCT_NAME<T>, new: STRUCT_NAME<T>, ...)
//     requires old.wf_list()
//     ensures new.wf_list()
// { ... }
```
