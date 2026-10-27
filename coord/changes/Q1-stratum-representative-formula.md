# StratumReductionFormula shared representative equation

## Reason

Kernel profiling of the complete comparison proof found repeated unfolding of concrete
module categories, exact pullback and localization data when converting between the
abstract counit equation and its concrete expansion. The last conversion alone took
50–65 seconds. Name that equation once as `DerivedReductionComparisonFormula`, and use
that same predicate in the abstract proof and in the published stratum predicate.
No theorem proof is moved out of the assigned module. The new definition has no holes.

## Old

```lean
def StratumReductionFormula
    (e : completedReductionTower X d ⋙ d.towerPull f ≅
      d.pull f ⋙ completedReductionTower Y d) : Prop :=
  ∀ P : CochainComplex (reductionModules X (d.completedRing X)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing X) P →
    e.hom.app (DerivedCategory.Q.obj P) ≫
        (completedReductionTower Y d).map
          ((stratumModulePull d f).mapDerivedCategoryFactors.hom.app P) ≫
        completedReductionTowerComplexCounit Y d
          (((stratumModulePull d f).mapHomologicalComplex (.up ℤ)).obj P) =
      (d.towerPull f).map (completedReductionTowerComplexCounit X d P) ≫
        (d.towerModulePull f).mapDerivedCategoryFactors.hom.app
          ((completedReductionComplexTowerFunctor X d).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (stratumModuleReductionIso d f).hom
            (.up ℤ)).app P)
```

## New

```lean
def StratumReductionFormula
    (e : completedReductionTower X d ⋙ d.towerPull f ≅
      d.pull f ⋙ completedReductionTower Y d) : Prop :=
  ∀ P : CochainComplex (reductionModules X (d.completedRing X)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing X) P →
      DerivedReductionComparisonFormula
        (stratumModulePull d f) (d.towerModulePull f)
        (completedReductionModuleTowerFunctor X d) (completedReductionModuleTowerFunctor Y d)
        (completedReductionTower X d) (completedReductionTower Y d)
        (completedReductionTowerComplexCounit X d) (completedReductionTowerComplexCounit Y d)
        (stratumModuleReductionIso d f) e P
```

The public signature and binders stay identical. Unfold
`DerivedReductionComparisonFormula` and `completedReductionComplexTowerFunctor` to
recover exactly the old equation, with the same ordinary comparison, actual counits,
and localization factors. No representative is changed, no hypothesis is introduced,
and no conclusion is weakened. In particular normalization is still required for
every K-flat complex, and uniqueness concerns that same normalization.
A temporary Lean probe recreated the old definition verbatim and proved
`OldStratumReductionFormula d f τ ↔ StratumReductionFormula d f τ` by `Iff.rfl`;
it compiled in 30.0 s. The temporary probe is not delivered.
Every target which uses this predicate therefore keeps its previous meaning; the
independent definition review should verify this definitional identification.

## Users

`tools/downstream.py Sheaf.Paper.StratumCompletionUnitRestriction --uses
StratumReductionFormula` found two textual users among 4786 downstream modules.
The assigned module is held by Q1 and the other holder is recorded below.
`CompletedDirectImageLimits` aliases the predicate and uses `Iff.rfl` to identify that
alias, then obtains its comparison by the unchanged existence/uniqueness declaration.
Those operations preserve exactly the same predicate. No consumer edit is necessary.
A compile of that unchanged consumer finishes with no Lean errors in 91.1 s against
this packet, over the 60-second limit. The control compile against the original
library also exceeds the limit (97.8 s), with no Lean errors; its profile attributes
53.9 s to linting and 35.7 s to attribute application (overlapping timings).
Thus this is an existing consumer timing issue, not a packet regression.
A further `rg` inspection found `CompletedTargetAugmentationNormalization` using the
chosen specification through the alias, so it is included as an indirect consumer.
The existing unit route is retained. The shared generic definition only names a
well-typed equation, including in the zero category and for identity functors; it
asserts neither existence nor that the equation automatically holds.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.StratumCompletionUnitRestriction | Q1 | Same predicate by unfolding the shared equation. |
| Sheaf.Paper.CompletedDirectImageLimits | unclaimed | Alias, reflexive equivalence and chosen normalization unchanged. |
| Sheaf.Paper.CompletedTargetAugmentationNormalization | unclaimed | Indirect chosen-specification use has the same statement. |

## Status

landed 20261026T092304-L-3420534 2026-10-26 (merge of deliver/Q1/Sheaf.Paper.StratumCompletionUnitRestriction)
