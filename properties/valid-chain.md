# Valid Chain Property (Reachability-Based)

## Goal
Show that the list forms one coherent chain using reachability:
- Every node in `nodes` is reachable from `first` by following `next`.
- From every node in `nodes`, `last` is reachable by following `next`.

## Informal definition (logic only)
The chain is valid when the following all hold:
- `first`/`last` are either both absent (empty list) or both present.
- All links are mutually consistent (`next`/`prev` agree).
- All nodes are on a single forward chain from `first` to `last`.

## Proof outline (steps and logic)
1. **Define the reachability predicates**: one that captures reachability from
   `first`, and one that captures reachability to `last`, both by traversing
   `next`. The chain validity property is the conjunction of these facts for
   all nodes in `nodes`.
2. **Establish base cases**:
   - Empty list: `nodes` is empty, so the property holds vacuously.
   - Single node: `first == last`, and the node reaches itself.
3. **Show structural consistency**:
   - `first` and `last` are members of `nodes` when present.
   - `next`/`prev` are consistent, so a forward step has a matching backward
     step.
4. **Prove reachability after each update**:
   - Identify which links and nodes changed.
   - For **existing nodes**, show their path from `first` still exists or can
     be repaired through the updated links.
   - For **new nodes**, show they are connected into the chain from `first`
     and that they can reach `last`.
   - For **deleted nodes**, show they are removed from `nodes` and are not
     required to satisfy reachability.
5. **Handle changes to `first`/`last`**:
   - If `first` changes, show all nodes remain reachable from the new `first`.
   - If `last` changes, show every node reaches the new `last`.
6. **Conclude chain validity** by combining the reachability facts for all
   nodes in `nodes`.

## Consistency lemmas for mutating operations
For every mutating operation, generate a lemma that proves its postconditions
imply `wf_list` (valid chain). This must exist for:
- `push_back`
- `push_front`
- `insert_before`
- `insert_after`
- `delete`

## Checklist for each mutating operation
- The `nodes` set is updated correctly (insert/remove one node).
- `first`/`last` are updated consistently with empty/non-empty cases.
- `next`/`prev` links remain mutually consistent.
- All nodes are reachable from `first`.
- `last` is reachable from every node.
- A consistency lemma exists for this operation (postconditions ⇒ `wf_list`).

## Common pitfalls to avoid
- Proving reachability from `first` but forgetting reachability to `last`.
- Updating `last` but not proving all nodes now reach the new `last`.
- Leaving a node in `nodes` without a path from `first`.
