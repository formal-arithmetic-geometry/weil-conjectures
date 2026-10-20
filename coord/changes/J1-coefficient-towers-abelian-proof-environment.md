# AlgebraicGeometry.ProEtale.sp_coefficient_towers_abelian

## Reason

The stage-3 preflight conservatively flags the added namespace, universe, variable,
open, option and local-attribute commands as changing what importers see. This
record documents their scope. They support fully proved private helpers and avoid
expanding the concrete currying equivalence and derived-category implementations
during proof elaboration. No existing public signature, definition body, structure
field, public import, generated structure declaration or exported attribute changes.
No source-library module is changed.

## Old

The original elaboration environment contains this exact block:

```lean
universe t u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale
```

The original theorem, with its unchanged signature, is:

```lean
theorem sp_coefficient_towers_abelian : Nonempty (SpCoefficientTowersAbelian l E T) := by
  sorry
```

The original five preceding public declarations are retained verbatim:
`spCoefficientCommRings`, `sp_coefficient_towers_abelian_axioms`,
`spCoefficientTowersAbelian`, `spCoefficientEvaluation`, and
`SpCoefficientTowersAbelian`. Their full old and new signatures and bodies therefore
coincide. The original global disable/restore of
`GrothendieckTopology.hasSheafify_of_essentiallySmall` is also preserved.

## New

The added top-level attributes are explicitly local:

```lean
attribute [local instance high] SheafOfModules.systemRingHasDerived
attribute [local irreducible] HasDerivedCategory.standard
```

The private helper namespaces `CoefficientTowerProof` and
`CoefficientReductionProof` introduce their own site, category, coefficient and
derived-localization universe variables. Their declarations all have `private`
visibility. Their `variable`, `universe` and `open` commands terminate with those
namespaces or sections. The original public declarations still quantify only the
same original parameters and universes.

The helper proof scopes and final assembly scope use:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Individual helper declarations also use the existing backward elaboration options.
No compiler time, heartbeat, kernel-checking or generated-declaration option is changed.
All diagnostic profiling and prefix exits have been removed.

The private reduction helpers use these local opacity controls:

```lean
attribute [local irreducible] ordinary
attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
  SheafOfModules.systemRingHasDerived
attribute [local irreducible] representedReduction
attribute [local irreducible] reduction
```

The concrete-equivalence section uses:

```lean
attribute [local irreducible] spCoefficientCommRings spCoefficientRings
  CoefficientTowerProof.equivalence CoefficientTowerProof.rebase
```

The unchanged public structure is elaborated in a section with:

```lean
attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
  SheafOfModules.systemRingHasDerived spCoefficientCommRings
```

The private assembly and final proof section uses:

```lean
attribute [local irreducible] spCoefficientCommRings spCoefficientRings
  spCoefficientTowerSheafCondition coefficientEquivalence DerivedCategory
  CategoryTheory.Functor.mapDerivedCategory SheafOfModules.systemRingHasDerived
```

These controls change only local elaboration transparency and priority. In
particular, the explicit coefficient-ring diagram, native addition and abelian
instance, and the chosen ordinary derived-localization interface are retained.
The existing theorem's new proof is exactly:

```lean
theorem sp_coefficient_towers_abelian : Nonempty (SpCoefficientTowersAbelian l E T) := by
  obtain ⟨L⟩ := systemLevelLeftExtensionTheory.{t + 1, t, max u (t + 1)}
    (J := Scheme.ProEt.topology T)
  exact assembleCoefficientTowers l E T L (coefficientEquivalence l E T)
    (coefficientEquivalence_sections l E T) (coefficientEquivalence_restrictions l E T)
    (coefficientEquivalence_transitions l E T) (coefficientEquivalence_morphisms l E T)
```

Every helper used here is private and fully proved. New imports are proof-only;
all original public imports remain verbatim. No target statement or target-used
public definition changes meaning, so no target statement re-review is requested.

## Users

`tools/downstream.py` reports 85 transitive consumers. Its `--uses` search for
`SpCoefficientTowersAbelian` reports 15 modules including the item. All six existing
public declaration names were searched in every consumer. The uses bind the same
unchanged public definitions and structure fields; none refers to the new private
helpers or inherits the local commands. The table includes every downstream module,
not only the direct textual users. Holder labels come from the current claim
records, respecting the configured expiry; no claim was changed.

This is a source/interface check, not a downstream rebuild. The delivered module
and its delivery probe compile; no consumer source adaptation is necessary. No
other group's file is included. Consequently none of these consumers' statements
becomes stronger, weaker or different.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCoefficientTowersAbelian | J1 | Completed proof; all preceding public declarations unchanged. |
| Sheaf.Paper.SmoothPurityCompactProjectionBaseChange | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionData | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionFinitePresentation | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionTensorSquare | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionTowerOperations | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionTowerPresentation | unclaimed | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityLevelPullbackExact | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedTowers | unclaimed | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerEvaluationAdjoint | unclaimed | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerInjectiveComponents | unclaimed | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerLevels | unclaimed | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerPushRightExtension | unclaimed | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerRightExtension | unclaimed | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerRightExtensionFiniteColimits | unclaimed | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Existing public declarations and fields unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Transitive consumer; imported public API unchanged; no adaptation. |

## Status

landed 20261020T211736-L-3495914 2026-10-20 (merge of deliver/J1/Sheaf.Paper.SmoothPurityCoefficientTowersAbelian)
