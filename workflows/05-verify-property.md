# Step 5: Verify the Target Property/Properties

## Procedure
1. Express the property as a `proof fn`, `assert`, or strengthened `ensures`
2. Use template `templates/property-proof.md`
3. Add proof hints as needed:
   - `assert(...)` intermediate facts
   - `assume(...)` only temporarily, must be removed
   - lemma calls

## Common property types
| Property               | How to encode                      |
|------------------------|------------------------------------|
| Functional correctness | strengthen `ensures`               |
| No overflow            | Verus checks automatically in exec |
| No panic / safety      | satisfy all `requires` at calls    |
| Algebraic law          | `proof fn` with `forall`           |
| List order             | `list_view` equality               |
| Link consistency       | `next/prev` mutual consistency     |
| Reachability / acyclic | `wf_list` + traversal lemmas       |

## DLL-focused proof helpers
- Lemmas for chain extension and list_view append.
- Frame lemmas for untouched nodes.
- No-cycle lemmas to justify reachability.

## Next
If it fails → `06-debug-failures.md`