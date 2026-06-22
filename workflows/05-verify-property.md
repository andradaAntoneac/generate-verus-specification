# Step 5: Verify the Target Property/Properties

## Procedure
1. Express the property as a `proof fn`, `assert`, or strengthened `ensures`
2. Use template `templates/property-proof.md`
3. Add proof hints as needed:
   - `assert(...)` intermediate facts
   - `assume(...)` only temporarily, must be removed
   - lemma calls
4. Ensure each executable function's `ensures` are discharged by the actual code
   (no modeling-only specs).

## Common property types
| Property               | How to encode                      |
|------------------------|------------------------------------|
| Functional correctness | strengthen `ensures`               |
| No overflow            | Verus checks automatically in exec |
| No panic / safety      | satisfy all `requires` at calls    |
| Algebraic law          | `proof fn` with `forall`           |
| List order             | `list_view` equality               |
| Link consistency       | `next/prev` mutual consistency     |
| Chain validity (reachability) | `wf_list` + reachability lemmas |

## DLL-focused proof helpers
- Lemmas for chain extension and list_view append.
- Frame lemmas for untouched nodes.
- Reachability lemmas to show all nodes reach `last`.

## Next
If it fails → `06-debug-failures.md`