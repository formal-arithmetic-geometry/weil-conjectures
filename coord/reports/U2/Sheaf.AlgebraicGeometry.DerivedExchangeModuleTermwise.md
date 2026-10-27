## What changed

Proved `AlgebraicGeometry.Etale.derivedExchangeModuleTermwise` in
`Sheaf.AlgebraicGeometry.DerivedExchangeModuleTermwise`, with its signature and all three
canonical-map definitions unchanged. The shorter route uses the already proved generic
`CategoryTheory.Adjunction.derivedExact_mateEquiv_app_fac`. Private, proved helpers normalize
its square and its complex-level factors, then combine naturality in `s.inv` and `j` with
cancellation in the replacement isomorphism. Added private proof imports of
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`,
`Sheaf.CategoryTheory.DerivedExactMate`, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`.
Updated the item's DAG proof, dependencies and origin to match this route. The proof-context
change record is `coord/changes/U2-derived-module-exchange-proof-context.md`; preflight
requires it for local irreducibility attributes and elaboration options. Public signatures,
public imports, unit realization and all other modules are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.derivedExchangeModuleTermwise`
(node `lem-weil-pbc-derived-exchange-module-termwise`). No holes added or split off; no `sorry`
remains in the item. All private helper theorems have complete proofs. Server compilation
via `lcompile.py` passed without errors or warnings (30.6 seconds).

## No longer needed

Removed private imports:

- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`

The direct proof no longer needs the old separate proof dependencies
`def-weil-pbc-adjunction-mate`, `def-weil-pbc-derived-categories`,
`lem-weil-pbc-exact-functor-derived-functor`, `lem-weil-pbc-kinjective-hom-derived`,
`lem-weil-pbc-kinjective-total-derived`, `lem-weil-pbc-localization-universal-property`,
`lem-weil-pbc-right-adjoint-preserves-kinjective`,
`lem-weil-pbc-termwise-adjunction-homotopy`,
`lem-weil-pbc-underived-exchange-module-linear`,
`prop-weil-pbc-inverse-image-modules-exact`, and
`prop-weil-pbc-kinjective-resolutions-exist`. Some remain statement dependencies or are used
transitively by retained library declarations; this delivery does not withdraw any module.
The general derived-mate lemma already encapsulates the Hom-bijection/counit argument.
Removed obsolete `tool_uses` entries for `lem-weil-pbc-kinjective-total-derived`,
`prop-weil-pbc-kinjective-resolutions-exist`, and
`lem-weil-pbc-underived-exchange-module-linear`, retaining `def-kun-unbounded-exchange`.

## Where the brief, the DAG or earlier work was wrong

The original six-step plan is valid but longer than necessary: the existing, proved generic
exact-derived mate normalization supplies its main compatibility calculation. The statement
needs no correction. The proof uses no boundedness and no preservation of K-injectives by
inverse image. No new nodes, definition changes, forced adaptations, or module withdrawals.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
