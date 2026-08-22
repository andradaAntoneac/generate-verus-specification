# Example: Proof Status Report (Partial Verification)

This example shows the kind of report Step 8 produces when verification is
partial — some lemmas are fully proved, but mutation operations still rely on
assume stubs.

See `templates/proof-status-report.md` for the full template and a longer
filled example.

## Context
- Implementation: index-based doubly linked list (`index_impl.rs`)
- Target property: reachability-based chain validity
- Verus result: ⚠️ partial (file verifies, but 4 assume stubs remain)

## Extract from generated report

### What Was Demonstrated
- `valid_chain` spec definition and equivalence lemma
- Accessors: `first`, `last`, `is_empty` — full ensures discharged
- Reachability helpers: `lemma_reaches_trans`, `lemma_nodes_subset_of_reachable`

### What Is Still Assumed
- `push_back` proof block assumes `self.chain_valid()` after mutation (High risk)
- `allocate_node` assumes initial link fields for new slot (Medium risk)

### Proof Struggles
1. **Weak loop invariant** for backward reachability — resolved by splitting
   into forward membership lemma + `lemma_reaches_last_from_member`
2. **Missing link-update lemma for push_back** — partially resolved; precise
   `next`/`prev` postconditions written, reachability still stubbed with assume

### Recommended next steps
1. Prove `lemma_push_back_preserves_valid_chain`
2. Remove `assume_chain_valid_after_mutation` helper
