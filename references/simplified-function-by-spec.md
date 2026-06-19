# Simplified Function by Spec

## Why simplification is allowed
When a function's preconditions (`requires`) fully determine which branch can
execute, some `if/else` branches are unreachable in the verified context.
In that case, the specification can be simplified to only describe the
reachable behavior. This reduces proof burden and makes the spec clearer.

## Key idea
Specifications describe behavior **under the stated preconditions**. If the
preconditions imply a condition (e.g., `x > 0`), then the branch for
`x <= 0` cannot occur. The spec can omit that branch, and the proof can rely
on the implied fact.

## When simplification is appropriate
- The `requires` clause logically implies the condition that selects a
  particular branch.
- The eliminated branch is **provably unreachable** in all verified calls.
- There is no runtime behavior you must preserve for invalid inputs
  (inputs that violate `requires` are outside the spec's scope).

## When simplification is NOT appropriate
- The preconditions do **not** imply the branch condition.
- The function is used in contexts where the precondition is intentionally
  weak or unspecified.
- You need to model defensive behavior for invalid inputs (e.g., error codes,
  panic behavior, or partial correctness under weak preconditions).

## Practical guidance
1. State the minimal preconditions that make the function safe and meaningful.
2. Check if those preconditions imply a single branch of an `if/else`.
3. If yes, simplify the spec to that branch only.
4. If you still need the full runtime behavior, keep the branches but note
   that some are unreachable under the spec.

## Proof consequences
Simplifying the spec means the proof only needs to show the reachable branch
meets the postconditions. If the implementation still contains both branches,
you will also need to show the unreachable branch is never taken under the
preconditions (usually by a short lemma or a `requires` implication).

## Summary
You may simplify a function's specification when the preconditions eliminate
branches. This is a standard technique to keep specs minimal and proofs
focused, but only safe when the unreachable branches are genuinely impossible
under the stated `requires`.
