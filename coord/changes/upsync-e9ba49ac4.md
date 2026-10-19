# Upstream sync e9ba49ac4 (2026-10-19): changes made to our modules

The sync to slopmaster2 e9ba49ac4 landed in live as ONE commit, ee8622b47b (prepared in ~/upstream-sync/side, log in ~/cc1/upsync-progress.md).
This file lists every module of ours that the sync, or the green-fix pass after it, changed beyond the mechanical merge.
Workers and reviewers: if one of your modules is listed here, this is why it changed.

## In the sync commit (adaptations, all statements unchanged unless noted)
- Upstream files where our only change was leftover `import Sheaf.*` lines are the tip files (29 files incl. HenselianConnectedness, PerfectLocusOfRank, AdditiveScalarBaseChange, HigherDirectImage/Transition, FiniteEtaleDescent, FinitePushforward, Gabber, Brauer, ...): the Sheaf imports clashed with their upstream twins.
- 18 upstream conflicts resolved (~/upstream-sync/resolved/index.tsv). Ours kept for exception-list files ProjectionFormula, BaseChangeTheorems/MorphismDefs (plus the tip lemma boundedConstructibleBaseChange_eq_exchangeRight), ShriekComposition. CohomologyContinuity is the tip file plus our proof of isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit.
- Sheaf modules retired as re-exports of identical upstream twins: AlternatingCechSortingOperators, SiteCechFreeComplexExactAux, EtaleTensorSections, ConstructibleAffineFreePresentationGeneral, HigherDirectImageTransitions, RingScalarExtension (upstream renamed restrictScalars_has_leftAdjoint to isRightAdjoint_restrictScalars), IntegralOverHenselianPair, LocalUniformHigherDirectImageBound, RingedModuleSkyscraper, SignedCechExtension.
- Leaf non-module Sheaf files made module files, so that they no longer load both twins: OrientedMaximalPointFiniteness, OpenBaseChangeSiteTransport, StrictTransformComposition, NormalGenericFibreVanishing, HypersurfaceNonzeroRelativeDifferential, BertiniSections, NodalFamilyNoetherianApproximation, DeligneLaumon.Reduction.Composition, ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias, RingTheory.ColimOfLocalizations.
- `DerivedMonoidal.braiding` / `braidedCategory` and `DerivedCategory.braidedCategory` now use the primed (proved) names in about 25 Sheaf modules where the unprimed ones are no longer visible.
- Compactification category instance moved upstream to Compactification.RefinementCategory: import added in the 48 Sheaf users of Compactification.Refinement.
- Sheaf.AlgebraicGeometry.FiniteLocallyConstantSetsLocalModels holds its proof again, because upstream deleted its twin. New module Sheaf.AlgebraicGeometry.Sites.SupportDimensionFiniteUnion holds dim_finite_union_le, which upstream removed. Imports added for moved lemmas (isAlgClosed_residueField_of_isClosed, LocallyClosedStratification).
- SelfTorAugmentedResolutionCharts: `set_option maxHeartbeats 400000 in` on one theorem. After the sync its statement needs about 250000 heartbeats; finding the definition that changed is follow-up work.
- Upstream proofs adapted: LocalizingLowerShriek (instance step made explicit) and OpenInjectiveCoefficientLowerComparisonFactorization (uses pullbackSquareComparison_def, since ours is no_expose).
- 34 coefficient-restriction entries added to coord/upstream-statement-exceptions.tsv (CompactificationIndependence, OpenLowerShriekBaseChange, OpenLowerShriekInterchange).

## Green-fix pass after the sync (follow-up commits)
- Take-out batch 20261019T034248 (abandoned; red since 12:26): restored `@[reducible]` on Sheaf.NumberTheory.Padics.CoefficientExtension.coefficientExtensionRing, which H2 (Sheaf.Paper.DirectImageTorAmplitude, landing 20261019T034300-L-417146) had removed. Its two named instances (CommRing, Algebra) stay. The defs that failed without it are DerivedNakayamaResolution.quotientRingSheaf/quotientModule, CompactSupportCoefficientChange.finiteReductionCompactSupportComparison and ExceptionalAdjointAdmissibility.ExceptionalFiniteReductionsCompatible, plus the proof of IntegersProfiniteTower.coefficientExtension_integers_profinite_tower.
- Sorried proofs (statements unchanged; each is now a stage-3 item):
  - Sheaf.AlgebraicGeometry.AffineSupportVanishing.affine_support_vanishing: used the private lemma Etale.residueFieldHomOfOver_eq, which upstream removed from Sites/SupportDimension.
  - Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange.smooth_exceptional_base_change: used isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension, which upstream #1549 replaced (SmoothDuality/BaseChange*).
  - Sheaf.Paper.PurEtaleLisseStratumCompact.isCompactObject_lowerStar_openImmersionLowerShriek_of_isFiniteLocallyConstantSheaf: DerivedCategory.braidedCategory is no longer visible (the primed instance is in Monoidal.Instances.DerivedCategoryBraided).
- Sheaf.Paper.CondensedCompactSupportProjection: import Compactification.RefinementCategory (the Refinement structure moved there upstream).
  - Sheaf.Paper.DirectImageTorAmplitude.sf_directImage_torAmplitude (the proof delivered by H2 in the abandoned take-out batch): kernel deterministic timeout once @[reducible] is restored on coefficientExtensionRing.
  - Sheaf.Paper.NoetherianEtaleSectionSpecialization.isIso_sectionMap (private): used isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension, which upstream #1549 replaced.
