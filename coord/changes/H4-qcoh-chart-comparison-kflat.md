# tensorResolutionChartComparisonIso

## Reason

Keep the affine section ring bundled when applying K-flatness. The new proved
`tensorResolution_isKFlat_bundledRing` theorem destructs the bundled ring and
applies the existing affine theorem. Its certificate has the exact chart type,
which avoids repeated normalization of `Spec (CommRingCat.of (Γ(Y,U) : Type u))`.
The new statement lives in its own `QCohTensorResolutionKFlatBundledRing` module,
imported publicly because the exposed definition uses its proof certificate. Only proof certificates in the construction change; all data and all existing
signatures are definitionally unchanged. No target meaning changes.

## Old

```lean
noncomputable def tensorResolutionChartComparisonIso
    (Y : Scheme.{u}) (M N : Y.Modules) [M.IsQuasicoherent]
    (U : Y.affineOpens) (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (P : ProjectiveResolution MA) (K F : CochainComplex Y.Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj M)
    (s : F ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj N)
    (hK : CochainComplex.IsKFlat (R := Y.sheaf) K)
    (hF : CochainComplex.IsKFlat (R := Y.sheaf) F)
    (hq : QuasiIso q) (hs : QuasiIso s) (i : ℤ) :
    (CochainComplex.mapBifunctor (tensorResolutionChartComplex U MA P)
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor Y.Modules 0).obj N))
      (curriedTensor (Spec Γ(Y, U.1)).Modules)).homology i ≅
    (CochainComplex.mapBifunctor
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj K)
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor Y.Modules 0).obj N))
      (curriedTensor (Spec Γ(Y, U.1)).Modules)).homology i := by
  let R := Scheme.Modules.restrictFunctor U.2.fromSpec
  let RC := R.mapHomologicalComplex (.up ℤ)
  let E := tensorResolutionChartComplex U MA P
  let M0 := (CochainComplex.singleFunctor Y.Modules 0).obj M
  let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
  let r := tensorResolutionChartAugmentation M U MA sM P
  have hE : CochainComplex.IsKFlat (R := (Spec Γ(Y, U.1)).sheaf) E :=
    tensorResolution_isKFlat (Γ(Y, U.1) : Type u) MA P
  have hK' := isKFlat_restrict U.2.fromSpec K hK
  have hF' := isKFlat_restrict U.2.fromSpec F hF
  haveI : QuasiIso q := hq
  haveI : QuasiIso s := hs
  have hq' : QuasiIso (RC.map q) := by dsimp [RC, R]; infer_instance
  have hs' : QuasiIso (RC.map s) := by dsimp [RC, R]; infer_instance
  exact tensorResolutionComparison (Spec Γ(Y, U.1)).sheaf E (RC.obj K) (RC.obj M0)
    (RC.obj F) (RC.obj N0) r (RC.map q) (RC.map s) hE hK' hF'
    (tensorResolutionChartAugmentation_quasiIso M U MA sM P) hq' hs' i
```

## New

```lean
noncomputable def tensorResolutionChartComparisonIso
    (Y : Scheme.{u}) (M N : Y.Modules) [M.IsQuasicoherent]
    (U : Y.affineOpens) (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (P : ProjectiveResolution MA) (K F : CochainComplex Y.Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj M)
    (s : F ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj N)
    (hK : CochainComplex.IsKFlat (R := Y.sheaf) K)
    (hF : CochainComplex.IsKFlat (R := Y.sheaf) F)
    (hq : QuasiIso q) (hs : QuasiIso s) (i : ℤ) :
    (CochainComplex.mapBifunctor (tensorResolutionChartComplex U MA P)
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor Y.Modules 0).obj N))
      (curriedTensor (Spec Γ(Y, U.1)).Modules)).homology i ≅
    (CochainComplex.mapBifunctor
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj K)
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor Y.Modules 0).obj N))
      (curriedTensor (Spec Γ(Y, U.1)).Modules)).homology i := by
  let R := Scheme.Modules.restrictFunctor U.2.fromSpec
  let RC := R.mapHomologicalComplex (.up ℤ)
  let E := tensorResolutionChartComplex U MA P
  let M0 := (CochainComplex.singleFunctor Y.Modules 0).obj M
  let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
  let r := tensorResolutionChartAugmentation M U MA sM P
  have hE : CochainComplex.IsKFlat (R := (Spec Γ(Y, U.1)).sheaf) E :=
    tensorResolution_isKFlat_bundledRing Γ(Y, U.1) MA P
  have hK' := isKFlat_restrict U.2.fromSpec K hK
  have hF' := isKFlat_restrict U.2.fromSpec F hF
  have : QuasiIso q := hq
  have : QuasiIso s := hs
  have hq' : QuasiIso (RC.map q) := by dsimp [RC, R]; infer_instance
  have hs' : QuasiIso (RC.map s) := by dsimp [RC, R]; infer_instance
  exact tensorResolutionComparison (Spec Γ(Y, U.1)).sheaf E (RC.obj K) (RC.obj M0)
    (RC.obj F) (RC.obj N0) r (RC.map q) (RC.map s) hE hK' hF'
    (tensorResolutionChartAugmentation_quasiIso M U MA sM P) hq' hs' i
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso | unclaimed | Body uses bundled-ring K-flatness; unchanged signature. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonNaturality | H4 | Signature and meaning unchanged; no forced adaptation. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateFactorization | unclaimed | Signature and meaning unchanged; no forced adaptation. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateSectionsNaturality | unclaimed | Signature and meaning unchanged; no forced adaptation. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateSheafIso | unclaimed | Signature and meaning unchanged; no forced adaptation. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIsoFormula | H4 | New single-chart identification API. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionKFlatBundledRing | H4 | New proved bundled-ring K-flatness API. |

These are the five existing textual users reported by `tools/downstream.py
--uses tensorResolutionChartComparisonIso`, plus the new equation client. No
module held by another group is adapted; no changed signature forces an adaptation.

## Status

landed 20261015T095527-L-1336309 2026-10-15 (merge of deliver/H4/Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonNaturality)
