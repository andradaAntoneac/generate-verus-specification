# Verus Syntax Cheat Sheet

> **Source:** https://verus-lang.github.io/verus/guide/
>
> Complete reference for writing Verus specifications, proofs, and verified Rust code.

---

## Function clauses
| Clause | Purpose | Notes |
| --- | --- | --- |
| `requires EXPR` | Precondition | May appear multiple times. |
| `ensures EXPR` | Postcondition | May appear multiple times. |
| `decreases EXPR` | Termination metric | Required for recursive spec/proof fns. |
| `invariant EXPR` | Loop invariant | Use inside loops. |

## Function kinds
| Kind | Meaning | Runtime |
| --- | --- | --- |
| `spec fn` | Pure spec function | Erased |
| `proof fn` | Proof-only code | Erased |
| `exec fn` / `fn` | Executable function | Retained |

## Types
| Type | Meaning | Notes |
| --- | --- | --- |
| `int` | Unbounded integer | Spec-only |
| `nat` | Non-negative unbounded | Spec-only |
| `bool` | Boolean | Spec + exec |
| `Seq<T>` | Sequence | Spec-only |
| `Set<T>` | Set | Spec-only |
| `Map<K,V>` | Map | Spec-only |
| `Option<T>` | Optional value | Spec + exec |
| `Ghost<T>` | Ghost wrapper | Zero runtime cost |

## Quantifiers
| Syntax | Meaning | Notes |
| --- | --- | --- |
| `forall \|x: T\| P(x)` | Universal quantification | Use triggers when needed. |
| `exists \|x: T\| P(x)` | Existential quantification | Use triggers when needed. |
| `#[trigger]` | Trigger annotation | Attach to subexpression. |

## Common operators
| Operator | Meaning | Notes |
| --- | --- | --- |
| `==>` | Implication | Spec logic |
| `<==>` | Bi-implication | Spec logic |
| `&&&` | Conjunction | Short for chained `&&` |
| `\|\|\|` | Disjunction | Short for chained `\|\|` |
| `=~=` | Extensional equality | Sets/sequences |
| `@` | View of ghost/spec value | E.g., `self.nodes@` |

## Common expressions
| Pattern | Meaning | Example |
| --- | --- | --- |
| `old(expr)` | Pre-state value | `old(self).wf()` |
| `Seq::empty()` | Empty sequence | `Seq::empty()` |
| `Set::empty()` | Empty set | `Set::empty()` |
| `Seq::new(n, |i: int| expr(i))` | Sequence by index | `Seq::new(n, |i: int| f(i))` |
| `Set::new(|x: T| pred(x)).unwrap_or(Set::<T>::empty())` | Set by predicate | `Set::new(|x: T| pred(x)).unwrap_or(Set::<T>::empty())` |
| `seq![a, b]` | Sequence literal | `seq![x, y]` |
| `set![a, b]` | Set literal | `set![x, y]` |

## Option helpers
Use `is_some()` and `is_none()`; `is_Some()` and `is_None()` are deprecated.

## Cast
```
let x: u64 = 10;
let y: int = x as int;   // cast to mathematical int
```  

## Nat arithmetic note
If a variable is `nat` and you perform subtraction (e.g., `x - 1`), the result
is `int`, not `nat`. Use `as nat` when you need a `nat`, and ensure it is
non-negative (e.g., `x >= 1`) before casting.  

## Assertions
```
assert(x > 0);              // verifier must prove this
assume(x > 0);             // verifier assumes without proof (use carefully)
assert(x > 0) by { ... };  // assertion with inline proof block
```

## Spec Functions
Pure mathematical functions used in specifications:
```
spec fn square(x: int) -> int {
    x * x
}

spec fn is_even(x: int) -> bool {
    x % 2 == 0
}
```
No `requires`/`ensures` typically (body IS the definition)
Can be used inside `requires`, `ensures`, `assert`
Can add `recommends` for guidance:
```
spec fn divide(x: int, y: int) -> int
    recommends y != 0
{
    x / y
}
```

## Open vs closed spec
In Verus, an **open** spec allows callers to rely on the spec but not its body,
while a **closed** spec allows the verifier to use the body as part of proofs.
If a spec is not explicitly marked `open`, it is treated as **closed** by
default.


## Making Spec Functions Visible
```
pub open spec fn f(x: int) -> int { x + 1 }   // body visible
pub closed spec fn g(x: int) -> int { x + 1 } // body hidden
```