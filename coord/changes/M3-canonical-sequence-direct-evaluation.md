# WeilConjectures.completedPullbackTensorDirectEvaluation_exists

## Reason

The former existence theorem is false for an arbitrary sequence coefficient map ρ.
Its left side restricts scalars through ρ, whereas its right side uses the canonical
constant-section map. An identity of underlying abelian sections need not be linear.
For f = id and an unramified quadratic coefficient extension, the compatible
quotient automorphisms induced by Frobenius twist the action of the regular module.
The sectionwise identity cannot preserve that action.

Require ρ = integralComparisonSequenceRingMap l E f. This is the canonical map
already prescribed by the node and its consumer. Stacks Tags 03D1 and 03D6
(sites-modules.tex, lemma-pushforward-module and definition-pushforward) specify
pushforward using restriction of scalars along the structure morphism.
This repairs the false generalization; it is not a proof of the former statement.
Uniqueness remains valid for arbitrary ρ and is unchanged.

## Old

```lean
theorem completedPullbackTensorDirectEvaluation_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ρ : coefficientSequenceCommRingSheaf l E Y ⟶
      ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
        (coefficientSequenceCommRingSheaf l E X)) (n : ℕ) :
    ∃ e : completedPullbackTensorDirectEvaluationBase l E f ρ ⋙
        coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E X n ⋙
        coefficientProEtaleModuleDirectImage.{u, u} f
          (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))),
      ∀ (M : coefficientSequenceModules l E X) (U : Y.ProEt)
        (x : ((coefficientSequenceEvaluation l E Y n).obj
          ((completedPullbackTensorDirectEvaluationBase l E f ρ).obj M)).val.obj (op U)),
        HEq ((e.hom.app M).val.app (op U) x) x
```

## New

```lean
theorem completedPullbackTensorDirectEvaluation_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ρ : coefficientSequenceCommRingSheaf l E Y ⟶
      ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
        (coefficientSequenceCommRingSheaf l E X)) (n : ℕ)
    (hρ : ρ = integralComparisonSequenceRingMap l E f) :
    ∃ e : completedPullbackTensorDirectEvaluationBase l E f ρ ⋙
        coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E X n ⋙
        coefficientProEtaleModuleDirectImage.{u, u} f
          (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))),
      ∀ (M : coefficientSequenceModules l E X) (U : Y.ProEt)
        (x : ((coefficientSequenceEvaluation l E Y n).obj
          ((completedPullbackTensorDirectEvaluationBase l E f ρ).obj M)).val.obj (op U)),
        HEq ((e.hom.app M).val.app (op U) x) x
```

The complete proof substitutes the canonical map, uses pushforwardComp on both
sides and pushforwardCongr for equality of the composite ring maps. The evaluation
ring transports have identity components, and the sequence ring map at (n,U)
is the finite constant-section map at U. All comparison maps are sectionwise
identities; the proved private helper sectionwiseIdentity_trans combines their
section formulas. Private pushforwardComp_sectionwise and
pushforwardCongr_sectionwise prove the formulas on arbitrary ringed sites using
the existing component lemmas. Their SectionwiseIdentity predicate is just the
displayed heterogeneous identity property. Local irreducibility attributes keep
the p-adic integer/uniformizer constructions, constant sheaf, canonical ring map
and Mathlib comparison implementations hidden during elaboration. No existing
definition, public import, target or consumer signature changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedPullbackTensorDirectEvaluationExistence | M3 | Repair the existence statement and prove it; preserve the base definition and arbitrary-map uniqueness. |
| Sheaf.Paper.CompletedPullbackTensorComparison | J3 | Forced proof adaptation: pass the already-proved pullbackTensorSequenceRing_eq to the helper; every signature, visibility, import and definition is unchanged. |

The downstream search found 3587 transitive importers and one direct importer.
Only CompletedPullbackTensorComparison mentions the changed theorem. Its canonical
map was already identified with integralComparisonSequenceRingMap, so its theorem
and all consumers retain precisely their previous meaning. No definition in a
target statement changes. The DAG's only citing node is
`def-pur-completed-pullback-tensor-comparison`; its use still holds by that equality.

## Status

landed 20261026T082444-L-2179113 2026-10-26 (merge of deliver/M3/Sheaf.Paper.CompletedPullbackTensorDirectEvaluationExistence)
