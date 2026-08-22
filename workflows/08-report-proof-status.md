# Step 8: Report Proof Status

## When to enter this step
**Always** — as the final step of every skill run, after:
- Step 5 (verify property) completes or stalls,
- Step 6 (debug failures) if applicable, and
- Step 7 (discrepancy report) if a real bug was found.

Produce this report even when verification fully succeeds. A clean run still
needs a demonstrated/assumed/struggles summary so the user knows exactly
what was proved.

## Procedure

1. **Re-read the generated spec file**
   Scan for:
   - `ensures` / `proof fn` that verify cleanly
   - every `assume(...)` (including inside proof blocks)
   - every `#[verifier::external_body]`
   - `requires` that restrict scope or exclude edge cases
   - comments marking stubs, TODOs, or temporary proof shortcuts

2. **Review the verification session**
   From your debug history (Step 6), collect:
   - initial Verus errors and failing clauses
   - invariants or lemmas you had to add or strengthen
   - tactics that worked vs. tactics that did not
   - anything still failing or bypassed with assume/external_body

3. **Run `verus` one final time** (if not already clean)
   Record the exit status: verified, partial (warnings/assumes), or failed.

4. **Classify each obligation**

   | Verdict | Criteria |
   |---------|----------|
   | **Demonstrated** | Verus discharges it; no `assume`; body not `external_body` (unless user axiom with proved consistency lemmas) |
   | **Assumed** | Uses `assume`, unproved stub, or `external_body` without consistency proof |
   | **Struggle** | Required non-trivial effort — document even if eventually resolved |

5. **Write the report** using `templates/proof-status-report.md`
   - Save as `{spec_basename}_proof_status.md` next to the generated `.rs`
     file unless the user gave a different path.
   - Be honest: if something uses `assume`, it is **not** demonstrated.

6. **Cross-link with discrepancy report**
   - If Step 7 produced a discrepancy report, reference it in Summary.
   - Do not duplicate bug details here; this report focuses on proof coverage.

## Output: structured proof status report

Always include:
- **Demonstrated** — target property, verified functions, proved lemmas
- **Assumed** — every `assume`, `external_body`, restricted `requires`, open stubs
- **Proof struggles** — failures encountered, attempts, resolutions
- **Coverage assessment** — end-to-end vs. modulo-assumptions vs. not covered
- **Recommended next steps** — ordered by impact (remove high-risk assumes first)

## Quality checks
- Every `assume(...)` in the spec appears in the Assumed section.
- Every `#[verifier::external_body]` function appears in the Assumed section.
- At least one proof struggle is documented if any Step 6 debugging occurred.
- Target property status is explicitly stated (proved / partial / not reached).
- Risk level assigned to each assumption (High = affects target property or safety).

## Important
- Do not mark an obligation as "demonstrated" if it relies on an `assume`
  in its proof path, even transitively through a helper lemma.
- When axiom-boundary code uses `external_body`, list what **is** proved
  about it (postconditions, consistency lemmas) separately from what is
  axiomatized.
- Prefer concrete file:line references over vague summaries.
