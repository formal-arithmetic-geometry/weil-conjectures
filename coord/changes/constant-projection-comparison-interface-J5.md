# AlgebraicGeometry.Etale.constantDerivedProjectionMap

## Reason

Kernel checking the concrete projection-formula proof expanded the source
`leftDerivedTensorComparison` into its derived bifunctor and localization construction,
exceeding the single-file 60-second limit. The compact `@[no_expose]` interface below has
exactly the original comparison as its data and a proved defining equality. It prevents
this expansion while preserving the canonical morphism. No source-library declaration,
target signature, coefficient hypothesis, or mathematical definition is weakened.

The assigned proof now compiles as one file. The temporary Aux and Apply files from the
previous attempt are not delivered. This record requests independent review of the
changed definition, including its use under target definitions: the defining equality
identifies the new map with the old canonical mate, so its mathematical meaning is unchanged.

## Old

```lean
noncomputable def constantDerivedProjectionMap (X : Scheme.{u})
    [(constantSheaf X.smallEtaleTopology A).Monoidal]
    [(constantSheaf X.smallEtaleTopology A).PreservesFlat]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory A) :
    (((rightDerivedGlobalSections A X) ⋙
      curriedTensor (DerivedCategory A)).obj E).obj K ⟶
    (((Functor.postcompose₂.obj (rightDerivedGlobalSections A X)).obj
      ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
        (constantSheaf X.smallEtaleTopology A).leftDerivedFunctor).obj
          (curriedTensor _))).obj E).obj K :=
  (((derivedConstantGlobalSectionsAdjunction A X).rightAdjointProjectionMap
    (constantSheaf X.smallEtaleTopology A).leftDerivedTensorComparison).app
      E).app K
```

## New

```lean
section CachedComparison

variable {C : Type*} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type*} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

/-- The canonical derived tensor comparison, kept behind a compact interface to avoid
expanding its localization construction during kernel checking of projection maps.
Source: the canonical tensor comparison in Stacks Tags 07A4 and 0F12, implemented by
`Functor.leftDerivedTensorComparison` (blueprint: def-kun-constant-projection-morphism).
The data are the existing comparison verbatim; the following equation exposes that identity. -/
@[no_expose] noncomputable def CategoryTheory.Functor.cachedDerivedTensorComparison :
    F.leftDerivedDerivedTensor ⟶ F.derivedTensorLeftDerived :=
  F.leftDerivedTensorComparison

/-- The compact interface denotes exactly the canonical left-derived tensor comparison.
Source: the defining comparison in Stacks Tags 07A4 and 0F12
(blueprint: def-kun-constant-projection-morphism).
Proof: unfold the interface; its body is the existing comparison. -/
theorem CategoryTheory.Functor.cachedDerivedTensorComparison_eq :
    F.cachedDerivedTensorComparison = F.leftDerivedTensorComparison := by
  unfold cachedDerivedTensorComparison
  rfl

end CachedComparison

noncomputable def constantDerivedProjectionMap (X : Scheme.{u})
    [(constantSheaf X.smallEtaleTopology A).Monoidal]
    [(constantSheaf X.smallEtaleTopology A).PreservesFlat]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory A) :
    (((rightDerivedGlobalSections A X) ⋙
      curriedTensor (DerivedCategory A)).obj E).obj K ⟶
    (((Functor.postcompose₂.obj (rightDerivedGlobalSections A X)).obj
      ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
        (constantSheaf X.smallEtaleTopology A).leftDerivedFunctor).obj
          (curriedTensor _))).obj E).obj K :=
  (((derivedConstantGlobalSectionsAdjunction A X).rightAdjointProjectionMap
    (constantSheaf X.smallEtaleTopology A).cachedDerivedTensorComparison).app
      E).app K
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap --uses
constantDerivedProjectionMap` lists three external textual users (the assigned item,
the bounded-below formula, and FiniteMappingAdjunction), plus the defining module itself.
All transitive importers are included below. The two other textual users only form the
named map, without unfolding its construction. No consumer adaptation is required. Both unchanged external consumers were compiled
against the repaired module: bounded-below formula in 13.6 seconds and
FiniteMappingAdjunction in 25.4 seconds, without errors or warnings.
The quarantined copy of FiniteMappingAdjunction has the same use and is retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula | J5 | Proof supplied in this delivery; signature unchanged. |
| Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormulaBoundedBelow | M5 | Mentions the map without unfolding it; its signature and type stay identical. |
| Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap | unclaimed | Definition body uses the equal compact comparison; new proved interface equation. |
| Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction | M7 | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.AlgebraicGeometry.GeometricPointProjectionComparison | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.AlgebraicGeometry.GeometricPointPullbackTensorNormalization | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing | G7 | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | P7 | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.DirectImageCtfOpenTor | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.ExternalRHomConePairing | J7 | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.SixFunctors.EtaleInternalHomDevissage | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Mentions the map without unfolding it; its signature and type stay identical. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Transitive importer only; no use or unfolding of the changed map body. |

## Status

landed 20261020T211743-L-3496986 2026-10-20 (merge of deliver/J5/Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula)
