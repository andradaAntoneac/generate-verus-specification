# Classifying Verification Failures

When Verus reports a failure, it does **not** tell you *why* the proof
failed in human terms. Your job is to classify the failure into one of
four categories, because each demands a different response.

> ⚠️ **Golden rule:** Never weaken, delete, or alter a specification clause
> just to make verification pass. If the implementation is wrong, the spec
> staying red is *correct behavior* — report the bug instead.

---

## The Four Failure Categories

| # | Category | Symptom | Correct response |
|---|----------|---------|------------------|
| 1 | **Weak spec** | Code is correct, but Verus can't *see* why | Add invariant / lemma / trigger (Step 4 & 6) |
| 2 | **Spec mismatch** | Your Verus clause doesn't match the abstract spec | Fix the translation (Step 2) |
| 3 | **🐛 Implementation bug** | Code genuinely violates the abstract spec | Report it (Step 7) — **do not** fix the spec |
| 4 | **🔲 Edge/boundary bug** | Fails only on extremes (0, empty, max, overflow) | Report as bug, or add a justified `requires` |

---

## Decision Tree

```
                      Verus reports a failure
                                │
                                ▼
        ┌───────────────────────────────────────────────┐
        │ Q1. Is the failing clause a FAITHFUL            │
        │     translation of the abstract spec?          │
        └───────────────────────────────────────────────┘
                  │NO                         │YES
                  ▼                           ▼
        ⚠️ SPEC MISMATCH          ┌───────────────────────────────┐
        Fix Verus spec           │ Q2. Can you find CONCRETE       │
        → go to Step 2           │     inputs where code output    │
                                 │     ≠ abstract-spec output?     │
                                 └───────────────────────────────┘
                                       │YES                │NO
                                       ▼                   ▼
                              🐛 IMPLEMENTATION   ┌──────────────────────┐
                              BUG                 │ Q3. Does adding an    │
                              → go to Step 7      │  invariant/lemma/     │
                              (report it)         │  trigger fix it?      │
                                                  └──────────────────────┘
                                                    │YES         │NO
                                                    ▼            ▼
                                            WEAK SPEC      ┌──────────────────┐
                                            (not a bug)    │ Q4. Does it fail │
                                            → done ✅       │  only on extremes?│
                                                           └──────────────────┘
                                                             │YES        │NO
                                                             ▼           ▼
                                                    🔲 EDGE-CASE   Re-examine:
                                                    BUG / missing  subtle bug OR
                                                    precondition   missing
                                                    → Step 7 or    precondition
                                                      add requires
```

---

## How to Apply Each Question

### Q1 — Is the clause a faithful translation?

Re-read the abstract spec line that this `ensures`/`invariant` came from.
Ask:
- Did I use the right comparison? (`>=` vs `>`)
- Did I cover all conjuncts of the abstract statement?
- Did I quantify over the right domain?
- Did I confuse `result` with an input?

Carry that conclusion into the corresponding workflow step.