## Worker report

The module `Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme` defines the affine-local
predicate `isFirstFittingIdealSheaf`, the uniquely characterized glued ideal sheaf
`firstFittingIdealSheaf`, and the closed subscheme inclusion
`firstFittingSingularSubscheme`.  It also records the closed-immersion instance.

For the node's hypothesis, `f : X ⟶ S` is a scheme morphism and `[LocallyOfFiniteType f]`
renders “locally of finite type”.  For each affine open `U : X.affineOpens`, the predicate
uses `Γ(X, U.1)` and `Γ(f.relativeDifferentials, U.1)`, an explicit finite free presentation
`π : (Fin n → Γ(X, U.1)) →ₗ[Γ(X, U.1)] Γ(f.relativeDifferentials, U.1)`, its surjectivity,
and `π.presentationFittingIdeal 1` for the first Fitting ideal.  The theorem
`existsUnique_firstFittingIdealSheaf` states existence and uniqueness of the compatible
ideal sheaf; `firstFittingIdealSheaf` is its `Classical.choose`, whose data is determined
uniquely by this condition.  The final definition is
`(firstFittingIdealSheaf f).subschemeι`, and the instance renders that it is a closed
immersion.  The convention `n ≤ 1` is the unit-ideal branch in
`LinearMap.presentationFittingIdeal`; the empty affine-open and zero-module cases are
therefore included.

Dependencies used: `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` from
`WeilConjectures.AlgebraicGeometry.Modules.Differentials`; Mathlib
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι` and its
`IsClosedImmersion` instance; Mathlib `AlgebraicGeometry.LocallyOfFiniteType`; and
`LinearMap.presentationFittingIdeal` plus
`LinearMap.presentationFittingIdeal_independence_baseChange` from
`Sheaf.RingTheory.PresentationFittingIdeal`.  The affine finite-type dependency is
Mathlib's `AlgebraicGeometry.locallyOfFiniteType_iff` as recorded by
`lem-weil-pbc-lft-affine-pairs`.

The edge cases checked were `n = 0`, `n = 1`, `n ≤ 1`, zero differential modules,
empty affine opens, and localization to basic opens; the fitting-ideal definition gives
the unit ideal in the required small-generator cases and the localization clause is
covered by the recorded independence/base-change theorem.

Searches made: `rg -n "Fitting|Sing\\(|singular|relativeDifferentials|IdealSheafData"` in
`WeilConjectures/` and `lean/Sheaf` found no singular/Fitting declaration; the Mathlib
LeanFinder query “Definition of the first Fitting ideal of the sheaf of relative Kahler
differentials and the singular closed subscheme” returned only unrelated kernel and
Kähler declarations; Loogle query `Module.fittingIdeal, KaehlerDifferential` returned
zero hits; LeanSearch query “first Fitting ideal of relative Kahler differentials singular
subscheme” returned no Fitting or singular-scheme declaration; grep for
`Fitting|fittingIdeal|FittingIdeal` in Mathlib/RingTheory found none.  The existing
relative-differentials and ideal-sheaf declarations above were read and reused.

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
