# Step 1: Analyze Inputs

## Goal
Build a mental model before writing any Verus.

Read `references/abstract-specification.md`. It is the base for the demonstration flow.

## Checklist
- [ ] Identify all function signatures (name, params, return type)
- [ ] Identify data types (structs, enums) and their fields
- [ ] Detect control structures: loops, recursion, branches
- [ ] Identify abstract list observations: `first`, `last`, `next`, `prev`,
  `value`, `is_empty`, `size`
- [ ] Determine the NodeId type (opaque, index, pointer, etc.)
- [ ] Detect axiom-boundary class: unsafe blocks, raw pointers, or opaque
      library types. If present, plan to use full `external_body` strategy.
- [ ] Extract from abstract spec:
  - Preconditions (what must hold on input)
  - Postconditions (what holds on output)
  - Invariants (what always holds)
- [ ] Identify integer types — watch for overflow concerns (u32, i64...)

## Output of this step
A structured summary:
| Element | Detail |
|---------|--------|
| Functions | ... |
| Types | ... |
| Loops/recursion | yes/no, where |
| Abstract model | NodeId, node set, first/last, next/prev, list_view |
| Preconditions | ... |
| Postconditions | ... |
| Target properties | Deduce from user (one or more) |
| Axiom boundary | yes/no, reason (unsafe/raw/opaque) |

## Next
Proceed to `02-map-spec-to-verus.md`