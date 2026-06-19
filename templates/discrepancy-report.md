# Discrepancy Report Template

Use this to report bugs and spec mismatches to the user. Fill in every
field. **Every 🐛 Implementation Bug MUST include a concrete counterexample**
— never report a bug on "verification failed" alone.

---

## Report Skeleton

```markdown
# Verification Discrepancy Report

## Summary
- Files analyzed: {list}
- Target property: {the property being proven}
- Result: {✅ verified | ❌ issues found}
- Issues found: {N} total — 🐛 {bugs} bug(s), ⚠️ {mismatches} spec mismatch(es), 🔲 {edge} edge-case(s)

---

## Issue #{n}: {one-line title}

| Field | Value |
|-------|-------|
| **Type** | 🐛 Implementation Bug / ⚠️ Spec Mismatch / 🔲 Edge-Case Bug |
| **Severity** | Critical / High / Medium / Low |
| **Location** | `path/to/file.rs:{line}` in `function_name` |
| **Status** | ❌ open / ✅ fixed & verified / ⏳ needs user decision |

### Abstract spec requirement violated
> "{quote verbatim the relevant line(s) of the abstract specification}"

### Verus clause that failed
\`\`\`rust
{the failing requires/ensures/invariant clause}
\`\`\`

### Counterexample            ← required for 🐛 and 🔲
\`\`\`
Input:    {concrete input values}
Expected: {what the abstract spec mandates for this input}
Actual:   {what the implementation produces}
\`\`\`

### Root cause
{1–3 sentences explaining why the code/spec diverges. Name the exact
mechanism: off-by-one, wrong operand, overflow, missing case, etc.}

### Suggested fix
\`\`\`rust
// before
{the problematic code}

// after
{the corrected code}
\`\`\`

### Verification status after fix
{✅ verifies | ⏳ proposed, not yet re-run | ⚠️ introduces new obligation: ...}

---
(repeat the "Issue #{n}" block for each finding)

---

## Items needing a user decision
{List any cases where the fix depends on intent — e.g. "Should empty input
return 0 or be a precondition violation? The abstract spec is silent."}

## Recommended next steps
1. {e.g., apply fix to Issue #1, re-run `verus file.rs`}
2. {e.g., confirm intended behavior for empty input}
```

---

## Filled Example

```markdown
# Verification Discrepancy Report

## Summary
- Files analyzed: `max.rs`
- Target property: functional correctness of `max`
- Result: ❌ issues found
- Issues found: 1 total — 🐛 1 bug, ⚠️ 0 spec mismatch, 🔲 0 edge-case

---

## Issue #1: `max` returns the wrong operand in the else-branch

| Field | Value |
|-------|-------|
| **Type** | 🐛 Implementation Bug |
| **Severity** | Critical |
| **Location** | `max.rs:2` in `max` |
| **Status** | ✅ fixed & verified |

### Abstract spec requirement violated
> "max(a, b) returns the larger of two integers: result ≥ a ∧ result ≥ b
> ∧ (result = a ∨ result = b)"

### Verus clause that failed
\`\`\`rust
ensures r >= b,
\`\`\`

### Counterexample
\`\`\`
Input:    a = 1, b = 5
Expected: 5
Actual:   1
\`\`\`

### Root cause
The `else` branch returns `a` instead of `b`, so whenever `b > a` the
function yields the smaller value, violating `r >= b`.

### Suggested fix
\`\`\`rust
// before
if a > b { a } else { a }

// after
if a > b { a } else { b }
\`\`\`

### Verification status after fix
✅ verifies — all three `ensures` clauses discharge.

---

## Items needing a user decision
None.

## Recommended next steps
1. Apply the one-line fix at `max.rs:2`.
2. Re-run `verus max.rs` to confir