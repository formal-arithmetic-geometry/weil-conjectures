# Sheaf.Paper.PointSectionsCompletionCone elaboration commands

## Reason

Keep coefficient constructions, localization choices and derived functors folded while
proving the normalized cone comparisons. Explicit universe-compatible instances avoid
unrelated equal-universe sheafification searches. Both respectTransparency options are
true. The public signatures and all existing construction bodies remain unchanged.
Only proved private helpers and proof imports are added. Local transparency attributes
and local instance priority changes affect proof elaboration in this module.

The interface checker treats command changes conservatively; this record covers them.

## Old

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
```

## New

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  CategoryTheory.Limits.limit completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted pointIntegralSectionMap
  completedScalarIdentityUnit integralScalarExtensionOfUniverses
  integralScalarExtensionComparisonOfUniverses HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors
  completedScalarComparison completedDerivedScalarExtension completedScalarCounit
  CompletedLineTensor.ordinaryUnit integralOperationsRoosMap
  PointQuotientAugmentation.roosComparison CompletedStalk.sectionsRoos
section Proof
attribute [local irreducible] factors
section FoldedRoos
attribute [local irreducible] pointIntegralSections
  PointQuotientAugmentation.coneComparison
attribute [local semireducible] CompletedStalk.sectionsRoos
attribute [local instance 3000] Algebra.toModule
end FoldedRoos
attribute [local instance 3000] Algebra.toModule
attribute [local irreducible] frobenius completionUnit
  integralDerivedPullback integralDerivedPullbackComparison
  integralOperationsPullbackTowerFunctor
section FoldedModels
attribute [local irreducible] pointIntegralSections
  integralOperationsRoos integralScalarTowerFunctor
end FoldedModels
attribute [local irreducible] completionModel completionModelAt pullbackModel beta
  completionComparison
end Proof
```

## Users

`tools/downstream.py` reports zero direct and transitive Lean importers of the item.
The unfinished DAG parent `lem-trf-integral-point-transport-tower-realization` still
needs this node. Its statement, like every public statement here, is unchanged.
No target meaning changes and no consumer adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointSectionsCompletionCone | H1 | Private proof elaboration only. |

## Status

landed 20261025T143425-L-999600 2026-10-25 (merge of deliver/H1/Sheaf.Paper.PointSectionsCompletionCone)
