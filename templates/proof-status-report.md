# Proof Status Report Template

Use this to summarize what the verification run established, what still
relies on assumptions or axioms, and where the proof was difficult. Fill in
every section. **Always produce this report** at the end of a skill run —
whether verification fully succeeds, partially succeeds, or stops on a bug.

Write the report as a separate markdown file alongside the generated spec
(e.g. `{spec_basename}_proof_status.md` in the same directory as the `.rs`
file), unless the user specifies a different path.

---

## Report Skeleton

```markdown
# Proof Status Report

## Summary
- Spec file: `{path/to/generated_spec.rs}`
- Implementation analyzed: `{path/to/impl.rs}`
- Target property: {the property being proven}
- Verus result: {✅ verified | ⚠️ partial | ❌ failed}
- Demonstrated: {N} fully proved obligation(s)
- Assumed / axiomatized: {M} item(s)
- Proof struggles documented: {K} item(s)

---

## What Was Demonstrated

List every obligation that Verus **fully discharges** without `assume` or
unjustified `external_body`. Group by category.

### Target property
| Property | Status | Where proved |
|----------|--------|--------------|
| {e.g., reachability-based chain validity} | ✅ proved | `{fn or lemma name}` at `{file:line}` |

### Executable functions (body verified)
| Function | Key postconditions proved | Location |
|----------|---------------------------|----------|
| `{fn_name}` | {brief list of main ensures} | `{file:line}` |

### Lemmas and proof functions
| Lemma | What it establishes | Location |
|-------|---------------------|----------|
| `{lemma_name}` | {one-line statement} | `{file:line}` |

### Structural invariants maintained
- `{e.g., wf_list preserved across push_back}` — proved in `{lemma}`

---

## What Is Still Assumed

List every place where the proof **does not** stand on its own. Be explicit
about *why* each assumption exists.

### Assumptions (`assume(...)`)
| Location | Assumed fact | Why not proved | Risk |
|----------|--------------|----------------|------|
| `{file:line}` in `{fn}` | `{what is assumed}` | {e.g., mutation postcondition too hard; temporary stub} | {Low / Medium / High} |

### Axiomatized code (`#[verifier::external_body]`)
| Function / block | Postconditions specified | Why external | User axiom? |
|------------------|--------------------------|--------------|-------------|
| `{fn_name}` | {brief ensures summary} | {e.g., raw pointers; SlotMap opaque} | {Yes / No — axiom-boundary} |

### Restricted scope (`requires` that exclude behavior)
| Function | Precondition | Effect on coverage |
|----------|--------------|-------------------|
| `{fn_name}` | `{requires clause}` | {e.g., excludes empty list; panics not modeled} |

### Open / stub proof obligations
| Obligation | Current status | Blocked by |
|------------|----------------|------------|
| `{e.g., push_back link update}` | ⏳ stub with assume | {missing lemma / axiom-boundary} |

---

## Proof Struggles

Document difficulties encountered during the run. Include resolved and
unresolved struggles.

### Struggle #{n}: {one-line title}

| Field | Value |
|-------|-------|
| **Category** | {Weak invariant / Missing lemma / Trigger / Overflow bound / Axiom boundary / Solver timeout / Other} |
| **Location** | `{file:line}` in `{fn or lemma}` |
| **Resolution** | {✅ resolved | ⏳ partially resolved | ❌ unresolved} |

#### What failed initially
{Verus error message or failing clause, quoted or paraphrased}

#### Why it was hard
{1–3 sentences: e.g., loop invariant too weak, reachability not visible to
solver, mutual recursion between link and chain lemmas}

#### What we tried
1. {e.g., added assert in loop body}
2. {e.g., split ensures into two lemmas}
3. {e.g., strengthened invariant with ghost order sequence}

#### Outcome
{What finally worked, or what remains open and why}

---
(repeat the "Struggle #{n}" block for each significant difficulty)

---

## Coverage assessment

### Fully verified end-to-end
{List behaviors/properties that need no assumptions to hold}

### Verified modulo assumptions
{List behaviors that hold *if* the assumed facts in the previous section are true}

### Not covered
{List abstract-spec behaviors or edge cases not yet modeled or proved}

---

## Recommended next steps
1. {e.g., replace assume stub in push_back with link-update lemma}
2. {e.g., prove free_list well-formedness invariant}
3. {e.g., narrow requires once overflow lemma is added}
```

---

## Filled Example

```markdown
# Proof Status Report

## Summary
- Spec file: `src/dll_verus.rs`
- Implementation analyzed: `src/index_impl.rs`
- Target property: reachability-based chain validity (`valid_chain`)
- Verus result: ⚠️ partial
- Demonstrated: 12 fully proved obligation(s)
- Assumed / axiomatized: 5 item(s)
- Proof struggles documented: 3 item(s)

---

## What Was Demonstrated

### Target property
| Property | Status | Where proved |
|----------|--------|--------------|
| `valid_chain` definition (reachability from `first`, `last` reachable) | ✅ proved | `spec fn valid_chain` + `lemma_valid_chain_equiv` at `dll_verus.rs:88` |

### Executable functions (body verified)
| Function | Key postconditions proved | Location |
|----------|---------------------------|----------|
| `first` | returns `Some` iff non-empty; matches `first_opt` | `dll_verus.rs:410` |
| `last` | returns `Some` iff non-empty; matches `last_opt` | `dll_verus.rs:425` |
| `is_empty` | equivalent to `first == INVALID` | `dll_verus.rs:440` |

### Lemmas and proof functions
| Lemma | What it establishes | Location |
|-------|---------------------|----------|
| `lemma_reaches_trans` | reachability is transitive along `next` | `dll_verus.rs:120` |
| `lemma_nodes_subset_of_reachable` | every node in `nodes()` is reachable from `first` | `dll_verus.rs:145` |

### Structural invariants maintained
- `wf_list` definition and helper lemmas — proved in `lemma_wf_list_append`

---

## What Is Still Assumed

### Assumptions (`assume(...)`)
| Location | Assumed fact | Why not proved | Risk |
|----------|--------------|----------------|------|
| `dll_verus.rs:337` in `push_back` proof block | `self.chain_valid()` after mutation | link-update postconditions not yet derived from exec body | High |
| `dll_verus.rs:196` in `allocate_node` | new slot has correct initial links | allocation path not fully traced | Medium |

### Axiomatized code (`#[verifier::external_body]`)
| Function / block | Postconditions specified | Why external | User axiom? |
|------------------|--------------------------|--------------|-------------|
| _(none in this example)_ | | | |

### Restricted scope (`requires` that exclude behavior)
| Function | Precondition | Effect on coverage |
|----------|--------------|-------------------|
| `push_back` | `old(self).wf_list()` | empty-list edge handled separately in proof branch |

### Open / stub proof obligations
| Obligation | Current status | Blocked by |
|------------|----------------|------------|
| `push_back` / `push_front` preserve `valid_chain` | ⏳ stub with `assume_chain_valid_after_mutation` | missing frame + link-update lemmas |

---

## Proof Struggles

### Struggle #1: Loop invariant too weak for backward reachability

| Field | Value |
|-------|-------|
| **Category** | Weak invariant |
| **Location** | `dll_verus.rs:210` in `lemma_all_reach_last` |
| **Resolution** | ✅ resolved |

#### What failed initially
Postcondition not satisfied: could not show `last` reachable from arbitrary node `n`.

#### Why it was hard
Forward-only loop invariant tracked reachability from `first` but the target
property needs backward reachability to `last`.

#### What we tried
1. Added `reaches(n, last, next)` to loop invariant — failed (not preserved).
2. Proved separate lemma: if `wf_list` and `n` in chain, then `reaches(n, last)`.

#### Outcome
Split into two lemmas; forward traversal proves membership, dedicated
`lemma_reaches_last_from_member` closes the gap.

### Struggle #2: Mutation ensures for `push_back`

| Field | Value |
|-------|-------|
| **Category** | Missing lemma |
| **Location** | `dll_verus.rs:320` in `push_back` |
| **Resolution** | ⏳ partially resolved |

#### What failed initially
Postcondition `self.chain_valid()` not satisfied after non-empty insert.

#### Why it was hard
Must relate old/new link fields for four touched slots while proving untouched
nodes unchanged; solver lost track of reachability.

#### What we tried
1. Strengthened ensures with explicit `next`/`prev` updates per slot.
2. Added frame lemmas for untouched nodes.
3. Still could not close reachability — used temporary `assume`.

#### Outcome
Precise link postconditions written; reachability proof deferred. Stub
documented as High risk in assumptions table.

---

## Coverage assessment

### Fully verified end-to-end
- Accessor functions (`first`, `last`, `is_empty`)
- Reachability transitivity and helper lemmas
- `valid_chain` spec definition

### Verified modulo assumptions
- `push_back` / `push_front` preserve chain validity (assumes post-mutation validity)

### Not covered
- Free-list well-formedness
- Overflow on `Vec` growth
- Behavior when allocation returns `INVALID`

---

## Recommended next steps
1. Prove `lemma_push_back_preserves_valid_chain` to remove assume stub.
2. Add `requires` bound on list capacity or prove no overflow.
3. Model free-list invariants if full allocation path must be verified.
```
