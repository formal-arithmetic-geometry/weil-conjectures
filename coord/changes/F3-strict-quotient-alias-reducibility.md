# Strict quotient computation alias reducibility

## Reason

The proof compiles alone but the required delivery compile with its axiom probe
exceeded 60 seconds twice. Detailed profiling recorded 33.6 seconds in the kernel
for the completed proof. The strict functor and counit aliases eagerly unfold
nested localization and completion constructions. Give these four aliases regular
definition reducibility hints, preserving their inferred types and complete bodies.
The proof explicitly unfolds the constant-complex alias at the one instance search
that requires its exactness. No mathematical data, counit, coefficient ring,
augmentation, target meaning, public import or declaration type is changed.

## Old

```lean
abbrev cbcStrictReduction (T : Scheme.{u}) := completedReductionComplexTowerFunctor T d

abbrev cbcStrictDelta (T : Scheme.{u}) :=
  (completedTowerConstant d T).mapHomologicalComplex (.up ℤ)

abbrev cbcStrictPull := (completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)

abbrev cbcStrictCounit (H : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ) :=
  Functor.leftDerivedCounitOnComplex (completedTowerModulePullback g d) LF τ H
```

## New

```lean
def cbcStrictReduction (T : Scheme.{u}) := completedReductionComplexTowerFunctor T d

def cbcStrictDelta (T : Scheme.{u}) :=
  (completedTowerConstant d T).mapHomologicalComplex (.up ℤ)

def cbcStrictPull := (completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)

def cbcStrictCounit (H : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ) :=
  Functor.leftDerivedCounitOnComplex (completedTowerModulePullback g d) LF τ H
```

## Users

`tools/downstream.py Sheaf.Paper.StrictQuotientPullbackComputation --uses
cbcStrictReduction cbcStrictDelta cbcStrictPull cbcStrictCounit` identifies the
following transitive consumers. The named uses outside the item occur only in
SfExactPullbackQuotientAugmentationSquare, whose existing theorem is still a hole.
All four consumers compiled unchanged against the revised sandbox module with
`lcompile.py --all`: item 37.7 s, SfExactPullbackCounitNormalization 30.3 s,
SfExactPullbackQuotientAugmentationSquare 29.5 s, SfCompletedAugmentationAdjunct
30.0 s, SfCompletedPullbackMateFactorization 36.7 s. The temporary consumer copies
were removed afterwards, so none of these modules is delivered or adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.StrictQuotientPullbackComputation | F3 | Own proof uses the unchanged data; explicitly unfolds cbcStrictDelta for instance search. |
| Sheaf.Paper.SfCompletedAugmentationAdjunct | K5 | No source edit; same public signatures and data. |
| Sheaf.Paper.SfCompletedPullbackMateFactorization | unclaimed | No source edit; same public signatures and data. |
| Sheaf.Paper.SfExactPullbackCounitNormalization | P4 | No source edit; same public signatures and data. |
| Sheaf.Paper.SfExactPullbackQuotientAugmentationSquare | K6 | No source edit; strict-functor expressions have identical types and values. |

## Status

landed 20261023T231026-L-3532278 2026-10-23 (merge of deliver/F3/Sheaf.Paper.StrictQuotientPullbackComputation)
