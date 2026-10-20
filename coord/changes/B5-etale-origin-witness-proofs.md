# AlgebraicGeometry.Scheme.etaleOriginScalars_locallyBijective and companion proofs

## Reason

Proof-only supporting work in the unclaimed module
`Sheaf.Paper.RingedEtaleOriginWitness`, required by the assigned theorem's
constant-coefficient realization route. Fill the three existing proof holes; retain
every declaration signature, public import and non-theorem body. No definition or
statement is repaired, weakened or replaced. This record makes the additional
unclaimed-module edits and their consumer check explicit.

The scalar-map proof transfers local injectivity and surjectivity of sheafification
on the same underlying section maps. The realization proof uses the associated-module
sheafification adjunction: its unit is an isomorphism on a module sheaf, and restriction
of the action constructs a preimage of every module sheaf. Full faithfulness and
essential surjectivity then give the exact additive equivalence. The finite comparison
proof cancels the second sheafification from the already proved locally bijective
finite scalar map, transfers the resulting local conditions to commutative rings,
and applies the site weak-equivalence characterization. The zero ring is included.

## Old

The three original signatures, verbatim (each had proof `by sorry`):

```lean
theorem etaleOriginScalars_locallyBijective :
    Presheaf.IsLocallyInjective (ProEt.topology T) (etaleOriginScalars T Λ) ∧
      Presheaf.IsLocallySurjective (ProEt.topology T) (etaleOriginScalars T Λ)

theorem etaleOriginRealization_properties :
    (etaleOriginRealization T Λ).Additive ∧
      PreservesFiniteLimits (etaleOriginRealization T Λ) ∧
      PreservesFiniteColimits (etaleOriginRealization T Λ) ∧
      (etaleOriginRealization T Λ).IsEquivalence

theorem finiteOriginConstantComparison_isIso (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] : IsIso (AdicCoefficients.constantComparison T Λ)
```

## New

The signatures are identical:

```lean
theorem etaleOriginScalars_locallyBijective :
    Presheaf.IsLocallyInjective (ProEt.topology T) (etaleOriginScalars T Λ) ∧
      Presheaf.IsLocallySurjective (ProEt.topology T) (etaleOriginScalars T Λ)

theorem etaleOriginRealization_properties :
    (etaleOriginRealization T Λ).Additive ∧
      PreservesFiniteLimits (etaleOriginRealization T Λ) ∧
      PreservesFiniteColimits (etaleOriginRealization T Λ) ∧
      (etaleOriginRealization T Λ).IsEquivalence

theorem finiteOriginConstantComparison_isIso (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] : IsIso (AdicCoefficients.constantComparison T Λ)
```

Each now has a complete Lean proof. The module has zero remaining direct `sorry`
occurrences. The canonical scalar maps, realization functor, function coefficient
ring, comparison isomorphism, restriction functor and retained witness are untouched.
Thus every target retains exactly its original meaning.

## Users

`tools/downstream.py Sheaf.Paper.RingedEtaleOriginWitness --uses
etaleOriginScalars_locallyBijective etaleOriginRealization_properties
finiteOriginConstantComparison_isIso` listed 79 transitive importers. Its whole-word
name scan found all three theorem names only inside the original witness module.
The table includes every transitive importer and the additional edited/new modules.
No held module is adapted. Proof irrelevance leaves each original exported interface
unchanged. The four delivered modules compile together against these proofs.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.AffineLinearActionRigidity | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.AffineLinearTraceAction | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.AffineLinearUniversalAction | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | M4 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.AffineSpaceTopTrace | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.AffineTraceLineLocalization | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.AffineTraceLinePurity | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | N1 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.ClosedSupportExceptionalComparison | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.FiniteCoefficientEtaleProjectionFormula | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals | G5 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | T3 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | W3 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction | B2 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition | A6 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | B3 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.ProEtaleProperBoundaryCohomology | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | P4 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | A7 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.ProjectiveLineTrace | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.SfFullcdEtaleOrigin | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.SfFullcdUsedClass | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | F1 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.BoundedSiteAdjunctionTranspose | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.CompactSupportExchangeTransport | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.CompactSupportSiteCoherence | U4 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.CompletedBaseChangeMap | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.CompletedDirectImageLimits | S9 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.CompletedProjectionCoherence | V1 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.CompletedPullbackUnitTower | D8 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.CompletedTowerCompatibility | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.CompletedTowerCorners | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.ExceptionalMateSiteComparison | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.FiniteLevelProEtaleBaseChange | B5 (this item) | Proof now uses the exact realization equivalence and unchanged finite constant isomorphism. |
| Sheaf.Paper.FiniteLevelRectangle | Q4 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.FourArrows | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.GlobalFiniteLevelCompactSupportBaseChange | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.LevelwiseAdicTruncations | F1 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.NormalizedEtaleOriginWitnesses | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.ProEtaleConstantReductionTower | G4 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.ProperOpenTowerComparison | H1 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.PurityFrameClass | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.PurityFrameKummer | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.SmoothMateCounitCancellation | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.StrictTowerExchangeMateNormalization | J3 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | M9 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | S4 | No adaptation: theorem signatures and all definition bodies remain identical. |
| Sheaf.Paper.RingedEtaleOriginWitness | unclaimed | Three proof holes filled; signatures, imports and definition bodies unchanged. |
| Sheaf.Paper.ProEtaleRealizedExchange | B5 (new) | Uses the explicit coordinate and exchange APIs; no adaptation of prior consumers. |
| Sheaf.Paper.ProEtaleRealizedExchangeCompatibility | B5 (new) | Uses the proved realization properties for its equivalence instance and explicit inverse. |

## Status

landed 20261020T221046-L-4138746 2026-10-20 (merge of deliver/B5/Sheaf.Paper.FiniteLevelProEtaleBaseChange)
