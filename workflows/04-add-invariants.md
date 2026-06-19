# Step 4: Add Loop & Recursion Invariants

## For each loop, specify:
- `invariant` — what holds every iteration
- `decreases` — termination measure (for `while`/recursion)

## Invariant discovery heuristics
1. What relationship between variables holds before AND after each iteration?
2. Bounds on loop counter: `0 <= i <= n`
3. Partial-progress: "first i elements are processed"
4. Preserved data-structure invariants

## DLL traversal loops
When traversing the list (e.g., search or list_view):
- Current node is either `None` or in `nodes`.
- Visited set is a subset of `nodes`.
- No duplicates in visited set (prevents cycles).
- Length of visited sequence equals number of steps taken.
- If traversal stops at `None`, then `visited.len() <= nodes.len()`.

## Use template
`templates/loop-invariant.md`

## Required checklist (must satisfy all)
- [ ] Every loop has at least one `invariant`
- [ ] Every loop has a `decreases` clause (even simple bounded loops)
- [ ] If a loop lacks `decreases`, stop and add it before proceeding

## Next
Proceed to `05-verify-property.md`