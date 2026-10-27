## What changed

Filled `CategoryTheory.Adjunction.derived_exact_forget_mate` in
`Sheaf.WeilSheaf.DerivedForgetMate`, with its statement and public imports unchanged.
The proof normalizes the specified four-factor isomorphism using the canonical
right-derived units, proves its compatibility with both derived adjunction units
on homotopy complexes, extends that equation by localization extensionality, and
identifies the mate using naturality and the right triangle identity. The only
additional declaration is a proved private helper cancelling an identity
homotopy-composition isomorphism. The item's DAG proof now records this calculation. A theorem-local
`linter.unusedSectionVars` setting retains the original unused
`HasKInjectiveResolutions C` interface hypothesis without a lint warning.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Adjunction.derived_exact_forget_mate`
(node `lem-sf-derived-exact-forget-mate`).
Holes closed: 1. Holes added: 0. Holes remaining in the delivered module: 0.
No split-off modules or statements. The proof compiled through `lcompile.py`
in 7.9 seconds; delivery runs the final compile and axiom probe.

## No longer needed

All three existing public imports supply the unchanged statement and remain.
No import or module is withdrawn. The direct calculation does not import these
four originally planned proof dependencies, removed from this node's proof route:

- `lem-sf-right-derived-from-adapted-complexes`
  (`Sheaf.CategoryTheory.DerivedCategory.RightDerivedFromAdaptedComplexes`):
  the canonical source right-derived functors and their units already exist.
- `lem-weil-pbc-kinjective-total-derived`
  (`Sheaf.CategoryTheory.KInjectiveTotalDerived`): no separate existence result
  is needed for those canonical functors.
- `lem-kun-derived-adjoint-square-comparison`
  (`Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison`): its unit
  calculation is carried out directly for the specified canonical adjunctions.
- `lem-pc-derived-adjoint-functors`
  (`Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`): the adjunctions in
  the statement are the already proved canonical source constructions.

This records unused planned dependencies, not global unreachability of their modules.
The unit record has no realized statement or step attached to this item; the
blueprint's forgetting-square argument is retained.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The source generic
`Functor.exactMateComparison_eq` and `Functor.derivedMate_pastedUnit` require
K-injective resolutions in an additional category under their possible
specialization; that is unavailable here and is not added. The direct calculation
uses only the hypotheses of the original statement. It also avoids the generic
adjoint-square theorem's extra essentially-constant-diagram and canonical-Hom
hypotheses by applying `derivedη_fac_app` directly.

Searches: LeanFinder returned the canonical derived-unit/counit factorization
lemmas; Loogle reported an unknown identifier for `mateEquiv`; the Mathlib grep
found generic derived-functor files. Reading the local source and the DAG's
recorded dependency declarations supplied the concrete normalization equations.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
