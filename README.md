# Verus Specification Generator Skill

This skill generates Verus specifications from a Rust implementation and an
abstract specification, then proves a target property. It is designed to keep
the resulting spec aligned with the implementation while producing proof
obligations that Verus can check.

## When to Use
- You have a Rust implementation and want to verify it with Verus.
- You have an abstract/mathematical specification you want to formalize.
- You need to prove a specific property (e.g., reachability-based chain validity).

## Required Inputs
1. Rust implementation (file path or snippet).
2. Target property to prove.
3. Output file path for the generated Verus spec.

## Example Prompt
```
/generate-verus-specification for @d:\path\to\index_impl.rs:1-230
targeting reachability-based chain validity and writing the solution to @src/main.rs
```

## Workflow (What the Skill Does)
1. **Analyze inputs**: Identify functions, types, loops/recursion, and the
   abstract list model (nodes, first/last, next/prev, list view).
2. **Map to Verus constructs**: Translate preconditions to `requires`,
   postconditions to `ensures`, and abstract helpers to `spec fn`.
3. **Generate the spec**: Preserve structure, define helpers, and encode all
   behavior for each function, not only the target property.
4. **Add invariants** (if loops/recursion exist): Provide loop invariants and
   `decreases` clauses.
5. **Verify the target property**: Strengthen ensures or add proof functions.
6. **Debug failures**: If verification fails, determine whether the spec is
   weak, incorrect, or if there is a real bug.
7. **Report discrepancies**: If the implementation is actually wrong, report
   the mismatch instead of masking it.

## Key Rules
- Preserve concrete fields when modeling structs; add ghost fields only as
  additions, not replacements.
- Model full behavior of functions, not just the target property.
- For doubly linked lists, define chain validity via reachability: every node
  reachable from `first` via `next`, and `last` reachable from every node.
- Prove properties against the actual implementation code (exec functions).
- Avoid `#[verifier::external_body]` unless the user provides an explicit axiom.
- Always run `verus <file>` and fix any errors.

## Output
The skill produces:
- A complete annotated Verus file in this repository (specified by the user).
- An explanation of each spec clause.
- Proof obligations addressed.
- A discrepancy report if any bugs or mismatches are found.

## Result Examples
The `result_examples/` folder contains full, generated Verus artifacts from
prior runs. Each file illustrates a distinct implementation model and proof
strategy:
- `result_examples/1.index_codex_5.2_high.rs` shows a baseline index‑based DLL
  spec with explicit reachability predicates and placeholder `assume`‑based
  proof stubs for some mutation obligations.
- `result_examples/2.index_claude_4.8_max.rs` provides a detailed index‑based
  specification with reachability lemmas, link consistency, and a free‑list
  well‑formedness invariant.
- `result_examples/3.index_claude_4.8_max.rs` presents a stronger invariant
  variant that introduces a ghost `order` sequence and proves `valid_chain`
  as a consequence of the inductive representation invariant.
- `result_examples/4.index_claude_4.6_high.rs` emphasizes traversal‑based
  reasoning (e.g., `chain_seq`, `no_dups`, and traversal frame lemmas) for
  reachability‑based validity.
- `result_examples/5.standard_claude_4.6_high.rs` models a pointer‑based DLL as
  an axiom boundary, using a ghost chain plus consistency lemmas for
  `push_back`/`push_front`.
- `result_examples/6.slotmap_claude_4.6_high.rs` models a slotmap‑backed DLL
  with ghost chain and link maps, treating SlotMap operations as external
  bodies while proving link‑consistency lemmas.

## Notes
The generated spec is intentionally storage‑agnostic unless the user asks for
implementation details. It focuses on abstract correctness and proof
obligations that Verus can verify.
