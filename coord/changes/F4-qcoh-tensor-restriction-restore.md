# tensorResolutionComparison_restriction

## Reason

Restore the quarantined item with its actual theorem, not an empty module. Compiling the
archived module fails at its imports:

```text
import Sheaf.AlgebraicGeometry.QCohTensorResolutionComparison failed, environment already
contains 'AlgebraicGeometry.tensorResolutionSiteModules' from
WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparison
```

The public naturality import now re-exports the source comparison, whereas the private
Sheaf formula import still loads the old comparison declarations. The source library
already proves the restriction theorem under the same name. Re-export that source module
instead of redeclaring it. No source-library file is edited; the quarantine archive stays.

## Old

The archived imports were:

```lean
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonNaturality
import Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonFormula
```

The archived theorem signature was:

```lean
theorem tensorResolutionComparison_restriction {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    (E K M F N : CochainComplex Y.Modules ℤ)
    (E' K' M' F' N' : CochainComplex X.Modules ℤ)
    (r : E ⟶ M) (q : K ⟶ M) (s : F ⟶ N)
    (r' : E' ⟶ M') (q' : K' ⟶ M') (s' : F' ⟶ N')
    (hE : CochainComplex.IsAcyclicTensorKFlat (R := Y.sheaf) E)
    (hK : CochainComplex.IsAcyclicTensorKFlat (R := Y.sheaf) K)
    (hF : CochainComplex.IsAcyclicTensorKFlat (R := Y.sheaf) F)
    (hE' : CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) E')
    (hK' : CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) K')
    (hF' : CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) F')
    (hr : QuasiIso r) (hq : QuasiIso q) (hs : QuasiIso s)
    (hr' : QuasiIso r') (hq' : QuasiIso q') (hs' : QuasiIso s')
    (e : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E ⟶ E')
    (k : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj K ⟶ K')
    (m : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj M ⟶ M')
    (f : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F ⟶ F')
    (t : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj N ⟶ N')
    (hrr : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map r ≫ m =
      e ≫ r')
    (hqq : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map q ≫ m =
      k ≫ q')
    (hss : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map s ≫ t =
      f ≫ s') (i : ℤ) :
    (Scheme.Modules.restrictFunctor j).map
        (tensorResolutionComparison Y.sheaf E K M F N r q s hE hK hF hr hq hs i).hom ≫
      (((CochainComplex.mapBifunctor K N (curriedTensor Y.Modules)).sc i).mapHomologyIso
        (Scheme.Modules.restrictFunctor j)).inv ≫
      HomologicalComplex.homologyMap (tensorResolutionRestrictionTensorMap j K N K' N' k t) i =
    (((CochainComplex.mapBifunctor E N (curriedTensor Y.Modules)).sc i).mapHomologyIso
        (Scheme.Modules.restrictFunctor j)).inv ≫
      HomologicalComplex.homologyMap (tensorResolutionRestrictionTensorMap j E N E' N' e t) i ≫
      (tensorResolutionComparison X.sheaf E' K' M' F' N' r' q' s'
        hE' hK' hF' hr' hq' hs' i).hom
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparisonRestrictionNaturality
```

The source theorem, now publicly available through the restored compatibility module, is:

```lean
theorem tensorResolutionComparison_restriction {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    (E K M F N : CochainComplex Y.Modules ℤ)
    (E' K' M' F' N' : CochainComplex X.Modules ℤ)
    (r : E ⟶ M) (q : K ⟶ M) (s : F ⟶ N)
    (r' : E' ⟶ M') (q' : K' ⟶ M') (s' : F' ⟶ N')
    (hE : CochainComplex.IsKFlatTensor (R := Y.sheaf) E)
    (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K)
    (hF : CochainComplex.IsKFlatTensor (R := Y.sheaf) F)
    (hE' : CochainComplex.IsKFlatTensor (R := X.sheaf) E')
    (hK' : CochainComplex.IsKFlatTensor (R := X.sheaf) K')
    (hF' : CochainComplex.IsKFlatTensor (R := X.sheaf) F')
    (hr : QuasiIso r) (hq : QuasiIso q) (hs : QuasiIso s)
    (hr' : QuasiIso r') (hq' : QuasiIso q') (hs' : QuasiIso s')
    (e : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E ⟶ E')
    (k : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj K ⟶ K')
    (m : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj M ⟶ M')
    (f : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F ⟶ F')
    (t : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj N ⟶ N')
    (hrr : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map r ≫ m =
      e ≫ r')
    (hqq : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map q ≫ m =
      k ≫ q')
    (hss : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map s ≫ t =
      f ≫ s') (i : ℤ) :
    (Scheme.Modules.restrictFunctor j).map
        (tensorResolutionComparison Y.sheaf E K M F N r q s hE hK hF hr hq hs i).hom ≫
      (((CochainComplex.mapBifunctor K N (curriedTensor Y.Modules)).sc i).mapHomologyIso
        (Scheme.Modules.restrictFunctor j)).inv ≫
      HomologicalComplex.homologyMap (tensorResolutionRestrictionTensorMap j K N K' N' k t) i =
    (((CochainComplex.mapBifunctor E N (curriedTensor Y.Modules)).sc i).mapHomologyIso
        (Scheme.Modules.restrictFunctor j)).inv ≫
      HomologicalComplex.homologyMap (tensorResolutionRestrictionTensorMap j E N E' N' e t) i ≫
      (tensorResolutionComparison X.sheaf E' K' M' F' N' r' q' s'
        hE' hK' hF' hr' hq' hs' i).hom
```

A text comparison verifies that the two signatures differ only by the six predicate names
`IsAcyclicTensorKFlat` / `IsKFlatTensor`; their defining bodies have the identical universal
condition `F.Acyclic → (mapBifunctor F K (curriedTensor _)).Acyclic`, with identical universes
and sheaf monoidal structure. The theorem proof bodies are verbatim identical. No
hypothesis, conclusion, comparison construction, or target meaning changes.

The existing node is attached to the source declaration, with its exact source signature.
Its statement dependencies, proof dependencies, proof steps, unit and source are preserved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonRestrictionNaturality | F4 | Restore the historical import path using the already proved source theorem. |
| WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparisonRestrictionNaturality | unclaimed; unchanged | Existing canonical declaration and complete proof retained verbatim. |
| WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartComparisonNaturality | unchanged | Already imports the source theorem directly; no adaptation. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonNaturality | unchanged | Already re-exports the source chart theorem; no adaptation. |

`tools/downstream.py` reports the quarantined item as an unknown module because it is
absent from `lean/`. A text search of both `lean/` and `quarantine/` finds no current Lean
importer of this Sheaf path. The DAG parent
`new-t3-qcoh-tensor-resolution-chart-comparison-naturality` still uses the node; its
mathematics remains available via the unchanged declaration, and no dependency is removed.
The unit's realized statement and proof steps remain unchanged. No other held module is
adapted, and no Lean module or DAG node is withdrawn.

Validation: the archive fails with the duplicate-declaration import error above; the
replacement compiles. A temporary `#check` confirms the entire theorem is available through
the restored module, and `#print axioms` reports exactly `propext`, `Classical.choice`,
`Quot.sound`. The diagnostic commands are removed from the delivered module.

## Status

landed 20261022T113952-L-452251 2026-10-22 (merge of deliver/F4/Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonRestrictionNaturality)
