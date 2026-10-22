# AlgebraicGeometry.Scheme.completedReductionPulledModelMap

## Reason

The combined finite-interface proof exceeds the 60-second file limit because concrete
coefficient data are repeatedly converted while checking the counit presentations.
Write the model map's morphism type explicitly and construct its universal comparison
once as `completedReductionCompositeCounitNat`. The model map is its component; the
naturality and invertibility proofs use the same typed natural transformation.

The new public construction has exactly the old component formula. Its naturality proof
composes the public quotient comparison isomorphisms with the two supplied universal
counits and the exact localization comparison. It uses no private declaration in its
signature or body, and chooses no new data. No statement or mathematical map changes.

## Old

```lean
def completedReductionPulledModelMap (n : ℕ)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :=
  (pbcTowerEvaluation X (pbcAdicCompletion X d) n).map
    ((completedTowerPullback g d).map
      (Functor.leftDerivedCounitOnComplex (completedReductionModuleTowerFunctor Y d)
        (completedReductionTower Y d) (completedReductionTowerCounit d Y) P) ≫
      completedTowerPullbackComplexCounit g d
        (((completedReductionModuleTowerFunctor Y d).mapHomologicalComplex (.up ℤ)).obj P)) ≫
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
      (op n)).mapDerivedCategoryFactors.hom.app
        (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
          (((completedReductionModuleTowerFunctor Y d).mapHomologicalComplex (.up ℤ)).obj P))
```

## New

```lean
def completedReductionPulledModelMap (n : ℕ)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
    (pbcTowerEvaluation X (pbcAdicCompletion X d) n).obj
      ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj
        (DerivedCategory.Q.obj P))) ⟶
    DerivedCategory.Q.obj
      ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj
          (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
            (((completedReductionModuleTowerFunctor Y d).mapHomologicalComplex
              (.up ℤ)).obj P))) := by
  letI := completedReductionModuleTowerFunctor_additive Y d
  letI := completedTowerModulePullback_additive g d
  exact (completedReductionCompositeCounitNat (completedReductionModuleTowerFunctor Y d)
    (completedTowerModulePullback g d)
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n))
    (completedReductionTower Y d) (completedTowerPullback g d)
    (completedReductionTowerCounit d Y) (completedTowerPullbackCounit g d)).app P
```

The public generic construction is in the same module. Its component is explicitly:

```lean
  app P := H.mapDerivedCategory.map
    (LG.map (Functor.leftDerivedCounitOnComplex F LF εF P) ≫
      Functor.leftDerivedCounitOnComplex G LG εG
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
    H.mapDerivedCategoryFactors.hom.app
      ((G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
```

## Users

The consumer search across both library roots finds `completedReductionPulledModelMap`
only in this module. `tools/downstream.py` likewise found only this module mentioning
it among 642 downstream modules. The public normalization predicate refers to exactly
the same map. The new generic construction is used only by this module's model map,
private comparison transformation and private invertibility lemma. Every existing
public statement and actual morphism type stays identical; no external adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedPullbackReduction | K2 | Share the explicit canonical counit comparison; retain the model map and normalization. |

## Verification

A check with the actual schemes, coefficient datum, level and arbitrary complex proves
by `rfl` that the new model map equals the entire original defining expression. The
check includes the ordinary comparison proof and compiles without warnings in 23.4 s.
Complete-file validation is performed by the delivery checks.

## Status

landed 20261022T011857-L-3228124 2026-10-22 (merge of deliver/K2/Sheaf.Paper.CompletedPullbackReduction)
