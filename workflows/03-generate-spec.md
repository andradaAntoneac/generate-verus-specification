# Step 3: Generate the Specification

##Before starting
1. The code of the implementation should be preserved as much as possible; but `asserts`, `assumes` and `proof` blocks can be added in the code to ensure the postconditions
2. The structures in the implementations should be preserved as much as possible
3. The result is an independent solution, dependencies in structures can be simplified as per the example in `examples/example-simplified-structure.md`
4. Panics can not be used, instead return a value that marks and invalid output (`NONE` when an index is expected to be returned).

## Axiom-boundary strategy
If Step 1 classified the implementation as axiom-boundary (unsafe, raw pointers,
opaque library types), switch immediately to a full
`#[verifier::external_body]` strategy:
- Mark executable functions as `external_body`
- Do not attempt to prove code bodies
- Spend effort on precise `requires`/`ensures` and consistency lemmas

## Procedure
1. For each function, add `requires` from preconditions
2. Add `ensures` from postconditions
3. Define `spec fn` helpers for abstract notions
4. Use the appropriate template from `templates/`
5. Simplify the functions if possible using `references/simplified-function-by-spec.md`
6. Ensure each executable function is proved against its implementation with
   assertions and proof lemmas (not only modeled by specs).

## Template selection
- Plain function → `templates/function-spec.md`
- Struct/enum → `templates/data-structure-spec.md`

## DLL abstraction checklist
- Define `wf_list` on the abstract structure (no storage assumptions).
  - Empty iff `first/last` are `None`.
  - `first/last` are members of `nodes`.
  - `next`/`prev` are mutually consistent.
- Define `list_view(self) -> Seq<T>` by traversing from `first`.
- For every mutating operation (`push_*`, `insert_*`, `delete`), read the exact
  link-update code path and generate precise link postconditions:
  - explicit `next`/`prev` updates for touched nodes
  - frame clauses for all untouched nodes (unchanged `next`/`prev`)
- If values must be tracked and operations take `value: T`, add `T: View`,
  introduce a ghost `values: Ghost<Seq<T>>`, and update `values@` in postconditions.
- Express updates via `nodes`, `next`, `prev`, and `list_view`:
  - `push_back` appends a value.
  - `push_front` prepends a value.
  - `insert_before/after` splice a value between neighbors.
  - `delete` removes one node from the sequence.
- Keep NodeId generic (opaque type); avoid allocation details unless requested.


## Properties 
1. The validity of the chain should be proved by reachability as per `properties/valid-chain.md`

## Quality checks
- Every parameter constraint captured?
- Return value fully specified?
- Spec functions are deterministic & total (add `decreases` if recursive)?
- Every `while` loop includes `invariant` and `decreases`
- Assume statements are minimal, not used for statements that can be proved
- Lemmas are defined axiomatically
- If a parameter is a mutable structure, check each field is unchanged at exit
  unless it must be modified; if modified, verify the field's integrity.
- If a parameter is mutable (`&mut`), every `ensures` clause that mentions it MUST
  use `old(PARAM)` for pre-state and `final(PARAM)` for post-state, even when the
  value is unchanged. 
- For immutable parameters (`&self` or plain values), `old(...)`/`final(...)` are
  optional; use them only when it improves clarity.
- Minimize the usage of `assumes` and `#[verifier::external_body]`
  (external bodies only for explicit axioms or axiom-boundary code).

## Next
If loops/recursion → `04-add-invariants.md`
Else → `05-verify-property.md`