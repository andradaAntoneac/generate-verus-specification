#Title
Verus Specification Generator

## Description
Generates Verus specifications from an abstract specification 
  and a Rust implementation, then proves a target property. Use when the 
  user wants to formally verify Rust code with Verus.
- User has a Rust implementation and wants to verify it
- User has an abstract/mathematical spec they want to formalize
- User wants to prove a specific property holds

## Required inputs (ask if missing)
1. **Rust implementation** — the actual code
2. **Target property** — what must be proven (correctness, safety, etc.)

## Workflow (follow in order)
1. Read `workflows/01-analyze-inputs.md`
2. Read `workflows/02-map-spec-to-verus.md`
3. Read `workflows/03-generate-spec.md`
4. Read `workflows/04-add-invariants.md` (if loops/recursion present)
5. Read `workflows/05-verify-property.md`
6. Read `workflows/06-debug-failures.md` (if verification fails)
7. Read `workflows/07-report-discrepancies.md` ← if failure is a real bug

## Critical principle
⚠️ When verification fails, you MUST determine the root cause:
- weak spec → strengthen it
- wrong spec → fix translation
- **real bug → STOP and report to the user, do not paper over it**

## DLL-specific rule
When modeling doubly linked lists, define mirrored reachability and chain
validity functions for both directions (e.g., `reachable_left/right`,
`valid_chain_left/right`) and combine them into a single `reachable`/`valid_chain`
predicate.

## Reference material
- Abstract specification of operations → `references/abstract-specification.md`
- Syntax questions → `references/verus-syntax.md`
- Pattern selection → `references/spec-patterns.md`
- Proof writing → `references/proof-patterns.md`
- Errors → `references/common-pitfalls.md`

## Output format
Always produce:
- Complete annotated Verus file in the current directory
- Explanation of each spec clause
- Proof obligations addressed
- **Discrepancy report (if any bugs/mismatches found)** — see `templates/discrepancy-report.md`