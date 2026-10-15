# tensorResolutionCoordinateSheafIso_factors

## Reason

Expose the existing three-factor coordinate isomorphism by a proved formula, avoiding
repeated unfolding of the K-flat construction during naturality proofs. The new module
QCohTensorResolutionCoordinateFactorization exports the formula through a proof-only import.
No existing signature or definition changes.
The two new square modules state separate parts of the argument with named remaining obligations.

## Old

No factorization theorem was exported. The definition of tensorResolutionCoordinateSheafIso
was the displayed three-factor composite; it remains unchanged.

## New

```lean
theorem tensorResolutionCoordinateSheafIso_factors
    (Y : Scheme.{u}) (M N : Y.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (U : Y.affineOpens) (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sN : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ProjectiveResolution MA) (K F : CochainComplex Y.Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj M)
    (s : F ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj N)
    (hK : CochainComplex.IsKFlat (R := Y.sheaf) K)
    (hF : CochainComplex.IsKFlat (R := Y.sheaf) F)
    (hq : QuasiIso q) (hs : QuasiIso s) (n : ℕ) :
    tensorResolutionCoordinateSheafIso Y M N U MA NA sM sN P K F q s hK hF hq hs n =
      (tensorResolutionChartHomologyIso N U MA NA sN P n ≪≫
        tensorResolutionChartComparisonIso Y M N U MA sM P K F q s hK hF hq hs (-(n : ℤ)) ≪≫
        (tensorResolutionNormalizedRestrictHomologyIso U.2.fromSpec K
          ((CochainComplex.singleFunctor Y.Modules 0).obj N) (-(n : ℤ))).symm) := by
  rfl
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateSectionsNaturality | T3 | Uses the formula to compose its two squares. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateFactorization | new in T3 delivery | States and proves the defining formula. |

All existing users continue to see exactly the same definitions and statements. No target
meaning changes and no forced adaptations are needed.

## Status

landed 20261015T065832-L-2599491 2026-10-15 (merge of deliver/T3/Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateSectionsNaturality)
