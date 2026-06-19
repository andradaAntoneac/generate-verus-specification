# Step 6: Debug Verification Failures

## Triage by error type
| Error message contains | Likely cause | Fix |
|------------------------|--------------|-----|
| "postcondition not satisfied" | weak invariant | strengthen loop invariant |
| "possible arithmetic overflow" | unbounded int | add `requires` bound |
| "precondition not satisfied" | missing caller guarantee | add `requires` or assert |
| "recommendation not met" | spec fn used wrong | check spec fn domain |

## Debugging tactics
- Add `assert(...)` to localize where reasoning breaks
- Split complex `ensures` into multiple clauses
- Add intermediate lemmas
- Check `decreases` actually decreases

## DLL-specific checks
- `list_view` mismatch → missing reachability/chain lemma.
- `next/prev` mismatch → update both directions in the spec.
- `first/last` mismatch → check empty/non-empty cases.

## See also
`references/common-pitfalls.md`