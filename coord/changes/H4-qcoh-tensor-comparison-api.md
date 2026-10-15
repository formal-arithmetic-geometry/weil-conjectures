# tensorResolutionComparison

## Reason

Implicit conversion of the comparison through nested bifunctor wrappers repeatedly
unfolded large tensor totalizations. Use the four explicit tensor maps, protect the
definition with `irreducible`, and provide the proved equation and restriction
naturality APIs. The new construction is definitionally equal to the old one.
All existing signatures and the mathematical meaning of target definitions stay identical.

## Old

```lean
noncomputable def tensorResolutionComparison
    (E K M F N : CochainComplex C ℤ)
    (r : E ⟶ M) (q : K ⟶ M) (s : F ⟶ N)
    (hE : E.IsKFlat) (hK : K.IsKFlat) (hF : F.IsKFlat)
    (hr : QuasiIso r) (hq : QuasiIso q) (hs : QuasiIso s) (i : ℤ) :
    (CochainComplex.mapBifunctor E N (curriedTensor C)).homology i ≅
      (CochainComplex.mapBifunctor K N (curriedTensor C)).homology i := by
  let T := (curriedTensor C).map₂CochainComplex
  let a := (T.obj E).map s
  let b := (T.map r).app F
  let c := (T.map q).app F
  let d := (T.obj K).map s
  have : QuasiIso a := tensorResolution_quasiIso_tensor_left s hs hE
  have : QuasiIso b := tensorResolution_quasiIso_tensor_right r hr hF
  have : QuasiIso c := tensorResolution_quasiIso_tensor_right q hq hF
  have : QuasiIso d := tensorResolution_quasiIso_tensor_left s hs hK
  exact (asIso (HomologicalComplex.homologyMap a i)).symm ≪≫
    asIso (HomologicalComplex.homologyMap b i) ≪≫
    (asIso (HomologicalComplex.homologyMap c i)).symm ≪≫
    asIso (HomologicalComplex.homologyMap d i)
```

## New

```lean
noncomputable def tensorResolutionComparison
    (E K M F N : CochainComplex C ℤ)
    (r : E ⟶ M) (q : K ⟶ M) (s : F ⟶ N)
    (hE : E.IsKFlat) (hK : K.IsKFlat) (hF : F.IsKFlat)
    (hr : QuasiIso r) (hq : QuasiIso q) (hs : QuasiIso s) (i : ℤ) :
    (CochainComplex.mapBifunctor E N (curriedTensor C)).homology i ≅
      (CochainComplex.mapBifunctor K N (curriedTensor C)).homology i := by
  let a := HomologicalComplex.mapBifunctorMap (𝟙 E) s (curriedTensor C) (.up ℤ)
  let b := HomologicalComplex.mapBifunctorMap r (𝟙 F) (curriedTensor C) (.up ℤ)
  let c := HomologicalComplex.mapBifunctorMap q (𝟙 F) (curriedTensor C) (.up ℤ)
  let d := HomologicalComplex.mapBifunctorMap (𝟙 K) s (curriedTensor C) (.up ℤ)
  have : QuasiIso a := tensorResolution_quasiIso_tensor_left s hs hE
  have : QuasiIso b := tensorResolution_quasiIso_tensor_right r hr hF
  have : QuasiIso c := tensorResolution_quasiIso_tensor_right q hq hF
  have : QuasiIso d := tensorResolution_quasiIso_tensor_left s hs hK
  exact (asIso (HomologicalComplex.homologyMap a i)).symm ≪≫
    asIso (HomologicalComplex.homologyMap b i) ≪≫
    (asIso (HomologicalComplex.homologyMap c i)).symm ≪≫
    asIso (HomologicalComplex.homologyMap d i)

attribute [irreducible] tensorResolutionComparison
```

The new `QCohTensorResolutionComparisonFormula` module states the proved
`tensorResolutionComparison_hom` equation. The new
`QCohTensorResolutionComparisonRestrictionNaturality` module states the proved
`tensorResolutionComparison_restriction` theorem, which uses that equation,
the four tensor restriction squares, and the existing homology zigzag theorem.
The chart theorem uses these APIs and a named private chart transition construction
so the checker can reuse the complex type of the transition map.

The chart comparison also uses the proved `tensorResolution_isKFlat_bundledRing`
lemma instead of repeatedly rebuilding the bundled section ring from its carrier.


The new `QCohTensorResolutionChartComparisonIsoFormula` module proves the
single-chart hom identification by reflexivity. The chart naturality proof uses this equation API
rather than unfolding the concrete comparison during the naturality argument.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionComparison | unclaimed | Definition presentation and irreducibility attribute; unchanged signatures. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso | unclaimed | Use the proved bundled-ring K-flatness API in the same comparison construction. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonFormula | H4 | New proved equation API. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonRestrictionNaturality | H4 | New proved restriction API. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIsoFormula | H4 | New proved single-chart identification API. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonNaturality | H4 | Prove the assigned naturality statement from the APIs. |

`tools/downstream.py --uses tensorResolutionComparison` lists the comparison
module and ChartComparisonIso as existing textual users. The existing `QCohTensorResolutionComparisonNaturality` module is unchanged.
No module held by another group is adapted. No target signature changes and no target meaning changes.

## Status

landed 20261015T095527-L-1336309 2026-10-15 (merge of deliver/H4/Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonNaturality)
