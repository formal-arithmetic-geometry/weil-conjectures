# AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.Modules; canonical restriction and localization aliases

## Reason

The scalar descent and coherence interfaces use the same recorded category, ring restriction,
module restriction and standard localization. Reuse their canonical definitions instead of
re-elaborating the same site constructions at every conversion. This changes no objects,
maps, tensor products, ring actions or coefficient universes. It adds a public import of
`Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarData` because these aliases are data
used by public declarations. All theorem signatures remain unchanged. Definitions used
by the project targets therefore require the normal independent statement review.

## Old

```lean
abbrev Modules {X : Scheme.{t}} (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  ringedSiteModules.{max u (t + 1)}
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)

abbrev rings {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j] :=
  (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).sheafPushforwardContinuous
    CommRingCat.{max u (t + 1)} (topology Y) (topology X)

abbrev restriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    Modules.{t, u} R ⥤ Modules.{t, u} ((rings.{t, u} j).obj R) :=
  clopenModuleRestriction j
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)})).obj R)

instance hasDerived {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    HasDerivedCategory.{max (u + 1) (t + 2)} (Modules.{t, u} R) :=
  HasDerivedCategory.standard (Modules.{t, u} R)

abbrev derivedRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  (restriction.{t, u} j R).mapDerivedCategory

```

## New

```lean
abbrev Modules {X : Scheme.{t}} (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  ClopenScalar.Mods.{t, u} R

abbrev rings {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j] :=
  ClopenScalar.rings.{t, u} j

abbrev restriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    Modules.{t, u} R ⥤ Modules.{t, u} ((rings.{t, u} j).obj R) :=
  ClopenScalar.res.{t, u} j R

@[instance_reducible]
instance hasDerived {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    HasDerivedCategory.{max (u + 1) (t + 2)} (Modules.{t, u} R) :=
  ClopenScalar.derived X R

abbrev derivedRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  ClopenScalar.resD.{t, u} j R

```

The `hasDerived` instance is marked `@[instance_reducible]`; its body is the same
standard localization. The imported generalized localization and scalar instances are
disabled locally while elaborating the file to avoid ambiguous universe inference.
Local irreducibility commands seal the standard localization and native tensor data
while proofs use their API; those commands do not change exported reducibility.

## Users

The following is the union of `tools/downstream.py --uses` for the five changed names.
The search matches the final segment of each name and therefore includes unrelated
local names such as `Modules` and prose occurrences of `restriction`. The actual
qualified uses are in the tensor module and `FiniteClopenConstructibilityBounds`;
the imported instance is explicitly disabled by the tower, decomposition, completed
operation and reduction modules. These aliases denote definitionally identical
original data, so the uses retain their meanings. There are no forced consumer
adaptations. The table includes these textual over-approximations for completeness.
Compiler verification and the definitional-equality probe are recorded in the final report.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClopenStrictTowerRoosEquivalence | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceReesFrame | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus | G5 | Same category, functors and standard localization; no source change. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.ClopenCompletedOperationTowers | Q5 | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.DiagonalDncChartNormalization | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.DiagonalOrientationRefinement | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.DualizingSigmaCocycleLocality | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.FiniteClopenConstructibilityBounds | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | J5 | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.PuritySectionEtaleRestriction | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.VaryingDimensionDualizingInverse | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.Paper.VectorModelChartDescent | unclaimed | Same category, functors and standard localization; no source change. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Same category, functors and standard localization; no source change. |


## Status

landed 20261025T041206-L-1069977 2026-10-25 (merge of deliver/G5/Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus)
