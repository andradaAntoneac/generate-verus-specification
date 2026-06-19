# Step 7: Report Bugs & Spec Discrepancies

## When to enter this step
A `ensures`/property fails AND you've ruled out:
- weak invariants (Step 4/6)
- a mistranslated spec (Step 2)

→ This points to a genuine implementation bug.

## Procedure
1. **Isolate the failing obligation**
   Identify the exact `ensures` clause or property that fails.

2. **Trace it to the abstract spec line**
   Quote the abstract spec requirement it corresponds to.

3. **Construct a counterexample**
   Find concrete inputs where:
   - abstract spec says output should be X
   - implementation produces Y ≠ X
   Use Verus `assert(false)` probing or manual reasoning.

4. **Confirm direction of error**
   Is it:
   - (a) implementation diverges from spec → BUG in code
   - (b) spec was unimplementable as written → SPEC issue
   - (c) edge case (overflow, empty, null) → BOUNDARY bug

5. **Write the report** using `templates/discrepancy-report.md`

## Output: structured bug report
Always include:
- Location (file:line, function name)
- The abstract requirement violated (quoted)
- Concrete counterexample inputs
- Expected vs actual behavior
- Severity (correctness / safety / edge case)
- Suggested fix (if clear)

## Important
Never silently "fix" the spec to make verification pass when the
implementation is actually wrong. Surface the bug to the user.