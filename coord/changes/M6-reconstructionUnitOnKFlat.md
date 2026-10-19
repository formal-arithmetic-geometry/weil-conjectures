# AlgebraicGeometry.Scheme.reconstructionUnitOnKFlat

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
def reconstructionUnitOnKFlat (P : CochainComplex (CompletedAdicModules T d) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P) :
    DerivedCategory.Q.obj P ⟶
      (reconstructionRlim T d).obj ((completedAdicReduction T d).obj (DerivedCategory.Q.obj P)) :=
  DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (reconstructionOrdinaryUnit T d)
        (ComplexShape.up ℤ)).app P) ≫
    reconstructionRlimComparison T d
      (((completedAdicOrdinaryTower T d).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
    (reconstructionRlim T d).map
      (@inv _ _ _ _ (reconstructionReductionComplexCounit T d P)
        (reconstructionTowerCounit_isIso T d P hP))
```

## New

```lean
def reconstructionUnitOnKFlat (P : CochainComplex (CompletedAdicModules T d) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P) :
    DerivedCategory.Q.obj P ⟶
      (reconstructionRlim T d).obj ((completedAdicReduction T d).obj (DerivedCategory.Q.obj P)) :=
  derivedCompletionModelUnit (completedAdicReductionData T d) (reconstructionLimit T d)
    (reconstructionRlim T d) (reconstructionLimit T d).rightDerivedFunctorUnit
    (reconstructionOrdinaryUnit T d) P hP
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
