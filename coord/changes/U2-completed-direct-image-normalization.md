# IsCompletedReductionPullbackComparison

## Reason

The old predicate expands the same K-flat representative equation as
`StratumReductionFormula`, but uses a separate ordinary comparison. The proved private
`ordinaryReduction_augmentation` computes its quotient-unit normalization, and
`ordinaryReduction_eq_stratum` identifies the ordinary comparisons by uniqueness.
Consequently the two predicates have precisely the same meaning. Reusing the existing
formula avoids a roughly 20-second kernel conversion; the complete file otherwise exceeds
its 60-second compilation limit. No hypothesis, conclusion, coefficient object, or chosen
comparison normalization changes.

The old generic `IsDerivedReductionPullbackComparison` declaration remains verbatim.
The public existence-and-uniqueness theorem keeps its signature and now reuses
`stratumReductionIso_exists`. Its old private localization proof is removed. The chosen
comparison is still determined uniquely. Data are chosen only from unique specifications.

## Old

```lean
def IsCompletedReductionPullbackComparison
    (τ : completedReductionTower V d ⋙ d.towerPull f ≅
        d.pull f ⋙ completedReductionTower U d) : Prop :=
  IsDerivedReductionPullbackComparison
    (completedReductionModuleTowerFunctor V d) (completedReductionModuleTowerFunctor U d)
    (proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)) (d.towerModulePull f) (completedReductionOrdinaryPullbackIso d f)
    (completedReductionTower V d) (completedReductionTower U d)
    (coherenceReductionTowerCounit V d) (coherenceReductionTowerCounit U d)
    (CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing V)) τ
```

## New

```lean
def IsCompletedReductionPullbackComparison
    (τ : completedReductionTower V d ⋙ d.towerPull f ≅
        d.pull f ⋙ completedReductionTower U d) : Prop :=
  StratumReductionFormula d f τ
```

## Users

`tools/downstream.py Sheaf.Paper.CompletedDirectImageLimits --uses
IsCompletedReductionPullbackComparison completedReductionPullbackIso_existsUnique
reductionTowerPullbackIso` finds no external user of the predicate or its unique-existence
theorem. The following users of the chosen comparison retain exactly the same signatures
and normalization. No consumer source needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedDirectImageLimits | U2 | Equivalent predicate and shorter proof; both holes filled |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | Same unique comparison |
| Sheaf.Paper.CompletedExchangeUnit | unclaimed | Same unique comparison |
| Sheaf.Paper.CompletedReductionPullbackSquare | unclaimed | Same unique comparison |
| Sheaf.Paper.CompletedReductionSquare | unclaimed | Same unique comparison |
| Sheaf.Paper.CompletedTowerCorners | unclaimed | Same unique comparison |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | K9 | Same unique comparison |
| Sheaf.Paper.StrictTowerExchangeMateNormalization | unclaimed | Same unique comparison |

The transitive definition closure of targets should be reviewed for this equivalent
normalization representation; no target text changes. Independent review should check the
ordinary quotient-unit calculation and the two representative formulas side by side.

## Status

landed 20261021T204033-L-3924438 2026-10-21 (merge of deliver/U2/Sheaf.Paper.CompletedDirectImageLimits)
