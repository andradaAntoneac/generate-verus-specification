# Step 2: Map Abstract Spec to Verus Concepts

## Mapping table
| Abstract concept        | Verus construct          |
|-------------------------|--------------------------|
| "for all input x..."    | `forall|x: T| ...`       |
| "there exists..."       | `exists|x: T| ...`       |
| precondition            | `requires`               |
| postcondition           | `ensures`                |
| pure helper function    | `spec fn`                |
| ghost/proof-only value  | `ghost`, `tracked`       |
| recursive definition    | `spec fn` + `decreases`  |
| result of function      | `result` in `ensures`    |

## DLL abstraction mapping (storage-agnostic)
| Abstract list element | Verus encoding |
|---|---|
| NodeId | generic type parameter `NodeId` |
| node membership | ghost `Set<NodeId>` or `spec fn nodes(self)` |
| `first` / `last` | `Option<NodeId>` (or sentinel) |
| `next` / `prev` | `spec fn` returning `Option<NodeId>` |
| list order | `spec fn list_view(self) -> Seq<T>` |
| empty list | `nodes().is_empty()` or `first().is_none()` |

## Rules
- Mathematical integers → use `int`/`nat` in spec functions
- Machine integers in exec code → assert no overflow
- Reference abstract spec line-by-line, map each to a clause
- Do not model allocation or storage layout unless the user explicitly asks.
  Keep the spec in terms of abstract nodes and their relationships.

## Next
Proceed to `03-generate-spec.md`