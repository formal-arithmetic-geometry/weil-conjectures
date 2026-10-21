# CategoryTheory.CofinalRoos.cofinalRoosRestriction

## Reason

The complete proof uses private algebraic and mapping-cone helpers, section-local
variables and elaboration options. Preflight requested a change record for these
new commands. The countable-products witness for complexes is a private proved
theorem registered with `attribute [local instance]` only in the proof section.
Every public signature, definition body, attribute and public import is unchanged.

## Old

No `Algebra` or `Complexes` proof-support section. No `complexProducts` helper.
The theorem's proof was `by sorry`.

## New

The added private witness has this signature:

```lean
private theorem complexProducts : HasCountableProducts (CochainComplex A ℤ)
```

It is constructed from the existing countable products of `A`, then registered
locally inside `section Complexes`. The new sections also contain private proved
helpers, local variables and elaboration options used only by these proofs.
`cofinalRoosRestriction` now has a complete proof. The existing public signature
and all three public constructions are verbatim unchanged.

## Users

`tools/downstream.py Sheaf.CategoryTheory.CofinalRoosRestriction --uses
cofinalRoosRestriction` found zero downstream modules and only the declaration
in the item itself. Pending DAG parents retain the same public interface and
mathematical statement; no consumer adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CofinalRoosRestriction | Y7 | Private proof support; sole hole filled. |

## Status

landed 20261021T134619-L-1401465 2026-10-21 (merge of deliver/Y7/Sheaf.CategoryTheory.CofinalRoosRestriction)
