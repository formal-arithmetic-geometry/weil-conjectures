# AlgebraicGeometry.Scheme.reconstructionReductionComplexCounit

## Reason

The completion-unit proof repeatedly compared a chosen left-derived pair and its
four localization factors at the concrete module-sheaf category. Profiling measured
30.9 seconds of kernel checking in the completion-unit theorem alone. Bundle the
same pair and its computation law in `DerivedReductionModelData`, and express the
complex counit and model unit through generic definitions. This preserves the
existing choices and gives definitionally equal bodies. The generic normalization
proof then specializes without expanding the coefficient-sheaf constructions.
No mathematical datum, statement, signature or visibility changes.

## Old

```lean
def reconstructionReductionComplexCounit (P : CochainComplex (CompletedAdicModules T d) ℤ) :
    (completedAdicReduction T d).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((completedAdicOrdinaryTower T d).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  (completedAdicReduction T d).map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (reconstructionReductionCounit T d).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((completedAdicOrdinaryTower T d).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((completedAdicOrdinaryTower T d).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
```

## New

```lean
def reconstructionReductionComplexCounit (P : CochainComplex (CompletedAdicModules T d) ℤ) :
    (completedAdicReduction T d).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((completedAdicOrdinaryTower T d).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  (completedAdicReductionData T d).complexCounit P
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.KoszulReconstruction | M6 | Definitionally equal interface; existing statement unchanged. |

The tables record direct textual users from `tools/downstream.py --uses`; no
external consumer is adapted. The target meaning is unchanged, since unfolding
the new record projections and generic definitions recovers the old terms.
The added generic API declarations are attached to
`def-weil-pbc-derived-reduction-model-data`.

## Status

landed 20261019T192806-L-1868443 2026-10-19 (merge of deliver/M6/Sheaf.Paper.KoszulReconstruction)
