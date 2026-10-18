# CategoryTheory.Abelian.SpectralObject.exists_pageTwoMap_data

## Reason

The static interface check records the new section-scoped `variable` commands
and declaration-scoped `unseal spectralSequence in` commands as other commands.
They organize private proof helpers and make the existing page construction
visible inside their proofs. They do not change any exported statement,
definition, persistent instance or attribute. This record documents that
syntactic command delta for independent review.

## Old

The public signature is:

```lean
theorem exists_pageTwoMap_data
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {X Y : SpectralObject C EInt} (φ : X ⟶ Y) :
    ∃ e : X.E₂SpectralSequence ⟶ Y.E₂SpectralSequence,
      ∀ (p q : ℤ),
        (e.hom 2).f (p, q) ≫
            ((HomologicalComplex.eval C _ (p, q)).mapIso
              ((SpectralSequence.pageFunctor C _ 2 2).mapIso (Iso.refl _)) ≪≫
            Y.spectralSequenceFirstPageXIso coreE₂Cohomological (p, q) _ _ rfl rfl
              (p + q) rfl).hom =
          ((HomologicalComplex.eval C _ (p, q)).mapIso
              ((SpectralSequence.pageFunctor C _ 2 2).mapIso (Iso.refl _)) ≪≫
            X.spectralSequenceFirstPageXIso coreE₂Cohomological (p, q) _ _ rfl rfl
              (p + q) rfl).hom ≫
            (φ.hom (p + q)).app (ComposableArrows.mk₁
              (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt))))
```

The private helper sections and their variable commands were absent.

## New

The public signature is identical:

```lean
theorem exists_pageTwoMap_data
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {X Y : SpectralObject C EInt} (φ : X ⟶ Y) :
    ∃ e : X.E₂SpectralSequence ⟶ Y.E₂SpectralSequence,
      ∀ (p q : ℤ),
        (e.hom 2).f (p, q) ≫
            ((HomologicalComplex.eval C _ (p, q)).mapIso
              ((SpectralSequence.pageFunctor C _ 2 2).mapIso (Iso.refl _)) ≪≫
            Y.spectralSequenceFirstPageXIso coreE₂Cohomological (p, q) _ _ rfl rfl
              (p + q) rfl).hom =
          ((HomologicalComplex.eval C _ (p, q)).mapIso
              ((SpectralSequence.pageFunctor C _ 2 2).mapIso (Iso.refl _)) ≪≫
            X.spectralSequenceFirstPageXIso coreE₂Cohomological (p, q) _ _ rfl rfl
              (p + q) rfl).hom ≫
            (φ.hom (p + q)).app (ComposableArrows.mk₁
              (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt))))
```

New private helper contexts, each closed before the public theorem:

```lean
section
variable {C ι : Type*} [Category* C] [Preorder ι] [Abelian C]
  {X Y : SpectralObject C ι} (φ : X ⟶ Y)
section Pages
variable {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (data : SpectralSequenceDataCore ι c r₀)
```

The private `spectralSequenceHom` definition and its first-page lemma each use
`unseal spectralSequence in` to unfold that existing definition locally.
A proof-only `import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence`
provides the private proof constants occurring in its homology-data construction.

## Users

All downstream modules from `tools/downstream.py` are listed; only
`Sheaf.CategoryTheory.SpectralObjectPageTwoMap` directly imports this module and
uses its theorem. Its unchanged source compiles against the proved module through
`lcompile.py` (2.6 seconds). None requires an adaptation. No target definition changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.SpectralObjectPageTwoMapExistence | N3 | Statement and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentExtVanishing | unclaimed | Statement and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Statement and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.CohomologicalDimensionGroundField | unclaimed | Statement and definitions unchanged; no adaptation. |
| Sheaf.CategoryTheory.CartanEilenbergCanonicalTruncationComparison | unclaimed | Statement and definitions unchanged; no adaptation. |
| Sheaf.CategoryTheory.CartanEilenbergFilteredTruncationComparison | unclaimed | Statement and definitions unchanged; no adaptation. |
| Sheaf.CategoryTheory.CartanEilenbergPageRealization | unclaimed | Statement and definitions unchanged; no adaptation. |
| Sheaf.CategoryTheory.FilteredComplexDecalageComparison | unclaimed | Statement and definitions unchanged; no adaptation. |
| Sheaf.CategoryTheory.GrothendieckSSDoubleComplexModel | unclaimed | Statement and definitions unchanged; no adaptation. |
| Sheaf.CategoryTheory.GrothendieckSpectralSequence | unclaimed | Statement and definitions unchanged; no adaptation. |
| Sheaf.CategoryTheory.SpectralObjectPageTwoFunctor | unclaimed | Statement and definitions unchanged; no adaptation. |
| Sheaf.CategoryTheory.SpectralObjectPageTwoMap | unclaimed | Statement and definitions unchanged; no adaptation. |
| Sheaf.Paper.ExtSheafToGlobalSpectralSequence | unclaimed | Statement and definitions unchanged; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Statement and definitions unchanged; no adaptation. |

## Status

landed 20261018T062839-L-666425 2026-10-18 (merge of deliver/N3/Sheaf.CategoryTheory.SpectralObjectPageTwoMapExistence)
