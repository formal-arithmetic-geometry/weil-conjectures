# AlgebraicGeometry.Scheme.cbcNormalizedFiniteComparison_exists

## Reason

Stage-3 preflight requests a change record for the added local attribute commands in
Sheaf.Paper.NormalizedFiniteComparisonExistence. The proof uses local instances for
additive ordinary model functors and protects large chosen constructions from automatic
unfolding. A generic API states the comparison in the exact nested representative formulas.
No existing declaration signature, definition body, visibility, public import or target
statement changes. Every new helper is private and proved.

## Old

The original declaration signature, verbatim:

```lean
theorem cbcNormalizedFiniteComparison_exists (n : ℕ) :
    (∃ e : completedReductionTower U d ⋙ cbcStrictOpen d j sq.isOpenImmersion ⋙
          completedTowerPullback g d ⋙ pbcTowerEvaluation X' (pbcAdicCompletion X' d) n ≅
        cbcFiniteReduction d U n ⋙ (cbcFiniteSource d sq n).mapDerivedCategory,
      CbcSourceFiniteNormalization d sq n e) ∧
    (∃ e : completedReductionTower U d ⋙ completedTowerPullback gU d ⋙
          cbcStrictOpen d j' sq.isOpenImmersion' ⋙
            pbcTowerEvaluation X' (pbcAdicCompletion X' d) n ≅
        cbcFiniteReduction d U n ⋙ (cbcFiniteTarget d sq n).mapDerivedCategory,
      CbcTargetFiniteNormalization d sq n e)
```

Original local attributes, verbatim:

```lean
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint
```

## New

The declaration signature is unchanged, verbatim:

```lean
theorem cbcNormalizedFiniteComparison_exists (n : ℕ) :
    (∃ e : completedReductionTower U d ⋙ cbcStrictOpen d j sq.isOpenImmersion ⋙
          completedTowerPullback g d ⋙ pbcTowerEvaluation X' (pbcAdicCompletion X' d) n ≅
        cbcFiniteReduction d U n ⋙ (cbcFiniteSource d sq n).mapDerivedCategory,
      CbcSourceFiniteNormalization d sq n e) ∧
    (∃ e : completedReductionTower U d ⋙ completedTowerPullback gU d ⋙
          cbcStrictOpen d j' sq.isOpenImmersion' ⋙
            pbcTowerEvaluation X' (pbcAdicCompletion X' d) n ≅
        cbcFiniteReduction d U n ⋙ (cbcFiniteTarget d sq n).mapDerivedCategory,
      CbcTargetFiniteNormalization d sq n e)
```

The complete local attribute commands now are:

```lean
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint Functor.mapDerivedCategoryFactorsh Functor.mapHomotopyCategory
  Functor.mapHomotopyCategoryFactors

attribute [local irreducible] completedReductionTower
  completedReductionTowerCounit completedTowerPullbackCounit pbcExtensionCounit
  completedAdicDerivedChange Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  limit AdicCoefficients.ringSystem completedAdicChange completedReductionModuleTowerFunctor
  completedTowerModulePullback cbcStrictOpenModule cbcSourceLevel cbcTargetLevel

attribute [local instance] cbcStrictOpenModule_additive completedTowerModulePullback_additive
  completedReductionModuleTowerFunctor_additive cbcSourceLevel_preservesZeroMorphisms
  cbcTargetLevel_preservesZeroMorphisms cbcFiniteSourceModel_preservesZeroMorphisms
  cbcFiniteTargetModel_preservesZeroMorphisms

attribute [local irreducible] complexCounit composeCounits composeFourCounits
  coordinateFourCounits

attribute [local irreducible] finiteReductionCounitNT reductionCounitNT pullbackCounitNT
  cbcSourceModelMap cbcTargetModelMap
  cbcFiniteSourceModelMap cbcFiniteTargetModelMap cbcFiniteReductionModelMap cbcReductionModelMap
```

The additional file option `set_option Elab.async false` makes proof checking synchronous.
It disables no kernel or linter check and changes no limit. All added imports are private
proof imports. Local instance and reducibility attributes expire with the namespace/module
scope and install no exported instance, simp lemma or declaration attribute. The public
statement and both public normalization predicates retain their original meaning.

## Users

The source-only command
`python3 tools/downstream.py Sheaf.Paper.NormalizedFiniteComparisonExistence --uses
cbcNormalizedFiniteComparison_exists` lists the three transitive consumers below.
Only CompletedRingStrictFiniteExchange mentions the declaration directly: it obtains the
two normalized comparisons and proves uniqueness. The other consumers import that result
transitively. Their source imports and applications were read; none needs adaptation.
No consumer is edited, and no target statement review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NormalizedFiniteComparisonExistence | R4 | Original existence theorem proved; interface preserved. |
| Sheaf.Paper.CompletedRingStrictFiniteExchange | M3 | Existing use of the identical theorem signature; no adaptation. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | Unclaimed in shared claim records | Transitive import; no interface change. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | Unclaimed in shared claim records | Transitive import; no interface change. |

## Status

landed 20261022T022952-L-767045 2026-10-22 (merge of deliver/R4/Sheaf.Paper.NormalizedFiniteComparisonExistence)
