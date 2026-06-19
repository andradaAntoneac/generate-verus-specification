# Example: Detecting an Implementation Bug

## Abstract spec
> max(a, b) returns the larger of two integers.
> ∀ a,b: result ≥ a ∧ result ≥ b ∧ (result = a ∨ result = b)

## Rust implementation
\`\`\`rust
fn max(a: i32, b: i32) -> i32 {
    if a > b { a } else { a }   // BUG: returns `a` in both branches
}
\`\`\`

## Generated Verus spec
\`\`\`rust
fn max(a: i32, b: i32) -> (r: i32)
    ensures
        r >= a,
        r >= b,
        r == a || r == b,
{ ... }
\`\`\`

## Verification result
❌ postcondition `r >= b` not satisfied

## Classification (per failure-classification.md)
- Is `r >= b` a faithful translation? YES
- Counterexample? a=1, b=5 → returns 1, but 1 < 5 ✗
→ 🐛 IMPLEMENTATION BUG

## Discrepancy report
**Type:** 🐛 Implementation Bug
**Location:** `max.rs:2`
**Violated:** "result ≥ b"
**Counterexample:** a=1, b=5 → expected 5, actual 1
**Root cause:** else-branch returns `a` instead of `b`
**Fix:**
\`\`\`rust
if a > b { a } else { b }
\`\`\`
✅ verifies after fix