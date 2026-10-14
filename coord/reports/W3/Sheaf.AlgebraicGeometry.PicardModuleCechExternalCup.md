## What changed

Restored and proved `AlgebraicGeometry.Scheme.Modules.picardModuleCech_externalCup`
by applying the existing proved `picardModuleCech_externalPairing`. Its conclusion
is exactly the assignment's conclusion, including all three additive scalar/module
Cech homology transports. No new mathematical statement or split-off is introduced.

The supplied module/node disappeared from the fresh base during the session when
the P3 parent delivery was rolled back. The delivery therefore restores this node
with W3 metadata and records the restoration in
`coord/changes/picard-module-cech-external-cup-restore.md`.

To resolve the recorded batch import collision, expand only the two hypothesis
predicates `IsPicardExternalCechCupBidegree` and `IsModuleCupProduct`, following the
existing E3 pairing repair. The lightweight `n2CupFront`/`n2CupBack` functions are
definitionally equal to the original `cupFront`/`cupBack`. Every original binder and
conclusion has the same type up to definitional equality; an example with the exact
original predicate-wrapped signature checks this. No target changes and no existing
consumer requires adaptation. Only the restored module is delivered.

Added the proof-only import of `PicardModuleCechExternalPairing`; replaced the public
coordinate/cup predicate imports by the lightweight definitions their expansions use.
The node's proof route is the one existing theorem. The same unit's Stacks argument
is reused; no unit-level step is bypassed. Existing declaration docstrings are kept.

Validation: the restored module compiled in 10.5 seconds without warnings. A separate
module containing an example with the exact original predicate-wrapped signature
compiled in 7.4 seconds. A non-module batch-style import and axiom probe compiled in
1.9 seconds, resolving the P3 import collision. The theorem's axiom list is propext,
Classical.choice, Quot.sound and sorryAx from existing imported obligations, with no
additional axiom. Successful probe sources are retained only in scratchpad/ and are
not delivery modules.

## Proved and sorry left

Closed the sole assignment hole:
`AlgebraicGeometry.Scheme.Modules.picardModuleCech_externalCup`
(node `lem-sc-picard-module-cech-external-cup`). Proved 1 of 1 local sorries;
0 split off, 0 holes added, 0 sorries remain in the delivered Lean file.
The reused `picardModuleCech_externalPairing` and
`picardExternalCech_moduleRepresentatives` contain no local sorry. Existing unresolved
obligations in their imported theory remain existing work; this delivery adds none.
This is a restoration with proof relative to the fetched base, and one closed hole
relative to the module supplied at assignment.

## No longer needed

Imports removed relative to the assignment snapshot:

- `Sheaf.Paper.CechCupPullbackCompat` (proof-only).
- `Sheaf.Paper.CechComparisonMapNaturality` (direct proof-only; still needed transitively).
- `Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree` (public; its hypothesis is expanded).
- `Sheaf.Paper.ModuleCohomologyCupProduct` (public; its hypothesis is expanded).

The old direct proof dependencies are replaced by
`lem-sc-picard-module-cech-external-pairing`. In particular,
`lem-sc-picard-cech-cup-pullback-compat` is not needed, and
`lem-sc-cech-comparison-map-naturality` is used through the reused pairing theorem
rather than directly; its module remains in the closure. The ordinary coordinate and cup notions
remain unchanged in the expanded statement. The reused theorem supplies the needed
refinement, cycle and comparison theory without an independent assembly here.

The project source import-graph comparison, against the assignment's original import
list, removes the following 262 project modules from this item's closure.
This is a local closure comparison; other targets may still need these modules.
Mathlib modules are not counted, since this calculation treats their imports as leaves.

- `Sheaf.Algebra.Category.ModuleCat.CocontinuousGenerator`.
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`.
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionExistence`.
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionUniqueness`.
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat`.
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.
- `Sheaf.Algebra.Homology.AcyclicKFlatTensor`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatTensorAcyclic`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatTensorAcyclicDegree`.
- `Sheaf.Algebra.Homology.BoundedFlatReplacement`.
- `Sheaf.Algebra.Homology.ChangeOfRingsAcyclicKFlat`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso`.
- `Sheaf.Algebra.Homology.ChangeOfRingsTensorAcyclic`.
- `Sheaf.Algebra.Homology.ChangeOfRingsTensorComparison`.
- `Sheaf.Algebra.Homology.CyclePullbackCore`.
- `Sheaf.Algebra.Homology.CyclePullbackLaws`.
- `Sheaf.Algebra.Homology.CyclePullbackLifting`.
- `Sheaf.Algebra.Homology.CyclePullbackResolution`.
- `Sheaf.Algebra.Homology.CyclePullbackTower`.
- `Sheaf.Algebra.Homology.CyclePullbackTowerComparison`.
- `Sheaf.Algebra.Homology.DerivedInternalHom`.
- `Sheaf.Algebra.Homology.FilteredColimitsTensor`.
- `Sheaf.Algebra.Homology.FilteredColimitsTensorTotal`.
- `Sheaf.Algebra.Homology.FlatAugmentationEpicification`.
- `Sheaf.Algebra.Homology.FlatCoverFunctor`.
- `Sheaf.Algebra.Homology.FlatTruncationSuccessor`.
- `Sheaf.Algebra.Homology.FlatTruncationTelescopeComparison`.
- `Sheaf.Algebra.Homology.FlatTruncationTower`.
- `Sheaf.Algebra.Homology.HomComplex`.
- `Sheaf.Algebra.Homology.HomComplexSectionsCanonicalComparison`.
- `Sheaf.Algebra.Homology.HomComplexSectionsCochains`.
- `Sheaf.Algebra.Homology.HomComplexSectionsCochainsComm`.
- `Sheaf.Algebra.Homology.HomComplexSectionsDerivedNaturality`.
- `Sheaf.Algebra.Homology.HomComplexSectionsHomotopyNaturality`.
- `Sheaf.Algebra.Homology.HomComplexSectionsQuasiIso`.
- `Sheaf.Algebra.Homology.InverseImageStalkScalarTransport`.
- `Sheaf.Algebra.Homology.InverseImageStalkScalarTransportBeta`.
- `Sheaf.Algebra.Homology.InverseImageStalkScalarTransportNaturality`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Sheaf.Algebra.Homology.KFlatClosure`.
- `Sheaf.Algebra.Homology.KFlatModuleBaseChange`.
- `Sheaf.Algebra.Homology.KFlatPullback`.
- `Sheaf.Algebra.Homology.KFlatResolution`.
- `Sheaf.Algebra.Homology.KFlatStalkCriterion`.
- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`.
- `Sheaf.Algebra.Homology.KFlatTensorConeTwoOutOfThree`.
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`.
- `Sheaf.Algebra.Homology.LocalizedHomComplexBoundaries`.
- `Sheaf.Algebra.Homology.LocalizedHomComplexCycleLift`.
- `Sheaf.Algebra.Homology.LocalizedHomComplexCycles`.
- `Sheaf.Algebra.Homology.LocalizedHomComplexCyclesBijective`.
- `Sheaf.Algebra.Homology.LocalizedHomComplexCyclesForward`.
- `Sheaf.Algebra.Homology.LocalizedHomComplexHomology`.
- `Sheaf.Algebra.Homology.LocalizedHomComplexHomotopy`.
- `Sheaf.Algebra.Homology.LocalizedModuleRestrictionQuasiIso`.
- `Sheaf.Algebra.Homology.LocalizedRestrictionAdjunction`.
- `Sheaf.Algebra.Homology.LocalizedRestrictionExtensionExists`.
- `Sheaf.Algebra.Homology.QuasiIsoHomComplexMap`.
- `Sheaf.Algebra.Homology.QuasiIsoOfSections`.
- `Sheaf.Algebra.Homology.RelativeFlatExtension`.
- `Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal`.
- `Sheaf.Algebra.Homology.StalkTensorComplex`.
- `Sheaf.Algebra.Homology.StalkTensorComplexDegrees`.
- `Sheaf.Algebra.Homology.StalkTensorComplexDifferential`.
- `Sheaf.Algebra.Homology.TelescopeColimit`.
- `Sheaf.Algebra.Homology.TelescopeShiftMono`.
- `Sheaf.Algebra.Homology.TensorPullbackStalkComplex`.
- `Sheaf.Algebra.Homology.TensorRestrictExtendScalars`.
- `Sheaf.Algebra.Homology.TensorRestrictExtendScalarsModule`.
- `Sheaf.Algebra.Homology.TruncationTelescope`.
- `Sheaf.AlgebraicGeometry.BasicPropertiesDegreeZero`.
- `Sheaf.AlgebraicGeometry.BasicPropertiesIdentity`.
- `Sheaf.AlgebraicGeometry.BasicPropertiesLinearity`.
- `Sheaf.AlgebraicGeometry.BasicPropertiesRestriction`.
- `Sheaf.AlgebraicGeometry.DerivedCategory`.
- `Sheaf.AlgebraicGeometry.DerivedTensorStructure`.
- `Sheaf.AlgebraicGeometry.EtaleTensorSections`.
- `Sheaf.AlgebraicGeometry.GlobalDerivedHom`.
- `Sheaf.AlgebraicGeometry.IdentityResolutionHomology`.
- `Sheaf.AlgebraicGeometry.InverseImageModuleFunctor`.
- `Sheaf.AlgebraicGeometry.InverseImageTensorPullbackComparison`.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties`.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapCompData`.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapComparison`.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapDataLinearity`.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapSemilinear`.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapZeroAugmentation`.
- `Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree`.
- `Sheaf.AlgebraicGeometry.RestrictionNaturality`.
- `Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived`.
- `Sheaf.AlgebraicGeometry.SchemeModuleFreeYonedaIso`.
- `Sheaf.Paper.CechCupProduct`.
- `Sheaf.Paper.CechCupPullbackCompat`.
- `Sheaf.Paper.CechCupResolutionRepresentatives`.
- `Sheaf.Paper.GlobalSectionsLaxMonoidalData`.
- `Sheaf.Paper.GlobalTensorPullbackDerivedData`.
- `Sheaf.Paper.GlobalTensorPullbackKFlat`.
- `Sheaf.Paper.GlobalTensorPullbackMatesIsIso`.
- `Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization`.
- `Sheaf.Paper.GlobalTensorPullbackOplaxIsIso`.
- `Sheaf.Paper.GlobalTensorPullbackTensorDescent`.
- `Sheaf.Paper.GlobalTensorPullbackUnderivedData`.
- `Sheaf.Paper.ModuleCohomologyCupProduct`.
- `Sheaf.Paper.ModuleCupAdjunctionCalculation`.
- `Sheaf.Paper.ModuleCupAdjunctionPolygon`.
- `Sheaf.Paper.ModuleCupCanonicalHZeroIdentification`.
- `Sheaf.Paper.ModuleCupCochainComparisonSquares`.
- `Sheaf.Paper.ModuleCupCochainCounitTensor`.
- `Sheaf.Paper.ModuleCupComponentChainEquation`.
- `Sheaf.Paper.ModuleCupComponentSectionMap`.
- `Sheaf.Paper.ModuleCupDerivedTensorConnectivity`.
- `Sheaf.Paper.ModuleCupEqualDerivedMapsClass`.
- `Sheaf.Paper.ModuleCupGlobalCounitComparison`.
- `Sheaf.Paper.ModuleCupGlobalTensorComparison`.
- `Sheaf.Paper.ModuleCupGlobalTensorPullback`.
- `Sheaf.Paper.ModuleCupHZeroIdentification`.
- `Sheaf.Paper.ModuleCupKInjectiveTarget`.
- `Sheaf.Paper.ModuleCupNaiveDerivedCompatibility`.
- `Sheaf.Paper.ModuleCupNaiveMap`.
- `Sheaf.Paper.ModuleCupPairingExists`.
- `Sheaf.Paper.ModuleCupRealizationComplexData`.
- `Sheaf.Paper.ModuleCupRealizationEvaluation`.
- `Sheaf.Paper.ModuleCupResolutionAugmentation`.
- `Sheaf.Paper.ModuleCupResolutionExistence`.
- `Sheaf.Paper.ModuleCupResolutionInvariance`.
- `Sheaf.Paper.ModuleCupResolutionRealization`.
- `Sheaf.Paper.PointInverseEvaluationKFlat`.
- `Sheaf.Topology.PointModuleEvaluationEquivalence`.
- `Sheaf.Topology.RingedModuleSkyscraper`.
- `Sheaf.Topology.SkyscraperComplex`.
- `Sheaf.Topology.SkyscraperComplexAcyclic`.
- `Sheaf.Topology.SkyscraperComplexStalk`.
- `WeilConjectures.Algebra.Homology.BifunctorLinear`.
- `WeilConjectures.Algebra.Homology.HomotopyCategory.Braided`.
- `WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure`.
- `WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom`.
- `WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal`.
- `WeilConjectures.Algebra.Homology.InternalHom`.
- `WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex`.
- `WeilConjectures.CategoryTheory.Abelian.Flat.Basic`.
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`.
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`.
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`.
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`.
- `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Coefficients`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`.
- `WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive`.
- `WeilConjectures.CategoryTheory.Monoidal.DerivedBraided`.
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`.
- `WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory`.
- `WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare`.
- `WeilConjectures.CategoryTheory.Sites.TransfinitePlus`.
- `WeilConjectures.CategoryTheory.Sites.TransfinitePlusSheaf`.
- `WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows`.
- `WeilConjectures.FromJoel.Algebra.Homology.Bifunctor`.
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits`.
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorCommShift`.
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy`.
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`.
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorShift`.
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`.
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated`.
- `WeilConjectures.FromJoel.Algebra.Homology.CochainComplexMinus`.
- `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`.
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex`.
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc`.
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.TruncGE`.
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.TruncLE`.
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Acyclic`.
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.DegreewiseSplit`.
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Devissage`.
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal`.
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.MonoidalTriangulated`.
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.PreservesQuasiIso`.
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Pretriangulated`.
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.ShiftSequence`.
- `WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.Basic`.
- `WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplex`.
- `WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus`.
- `WeilConjectures.FromJoel.Algebra.Homology.Monoidal`.
- `WeilConjectures.FromJoel.Algebra.Homology.ObjectProperty`.
- `WeilConjectures.FromJoel.Algebra.Homology.Single`.
- `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic`.
- `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat`.
- `WeilConjectures.FromJoel.CategoryTheory.Functor.CurryingThree`.
- `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerived`.
- `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedBifunctorComp`.
- `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedFour`.
- `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedThree`.
- `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedTrifunctorComp`.
- `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedTwo`.
- `WeilConjectures.FromJoel.CategoryTheory.Functor.Quadrifunctor`.
- `WeilConjectures.FromJoel.CategoryTheory.GuitartExact.Basic`.
- `WeilConjectures.FromJoel.CategoryTheory.Limits.Constructions.EventuallyConstant`.
- `WeilConjectures.FromJoel.CategoryTheory.Localization.Composition`.
- `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Derives`.
- `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesFour`.
- `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesThree`.
- `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo`.
- `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Monoidal`.
- `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions`.
- `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Product`.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Derived`.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Pentagon`.
- `WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.Retract`.
- `WeilConjectures.FromJoel.CategoryTheory.QuotientThree`.
- `WeilConjectures.FromJoel.CategoryTheory.QuotientTwo`.
- `WeilConjectures.FromJoel.CategoryTheory.Triangulated.HomologicalFunctor`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.FilteredColimits`.
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.HomComplex`.
- `WeilConjectures.Mathlib.Algebra.Homology.Localization`.
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`.
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu`.
- `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Limits`.
- `WeilConjectures.Mathlib.CategoryTheory.Comma.CardinalArrow`.
- `WeilConjectures.Mathlib.CategoryTheory.EssentialImage`.
- `WeilConjectures.Mathlib.CategoryTheory.Generator.StrongGenerator`.
- `WeilConjectures.Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`.
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer`.
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic`.
- `WeilConjectures.Mathlib.CategoryTheory.Localization.Bousfield`.
- `WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives`.
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Category`.
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic`.
- `WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.Composition`.
- `WeilConjectures.Mathlib.CategoryTheory.Presentable.Limits`.
- `WeilConjectures.Mathlib.CategoryTheory.Shift.CommShiftTwo`.
- `WeilConjectures.Mathlib.CategoryTheory.Shift.Localization`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.CompatiblePlus`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Grothendieck`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.LeftExact`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Localization`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Plus`.
- `WeilConjectures.Mathlib.CategoryTheory.SmallObject.TransfiniteIteration`.
- `WeilConjectures.Mathlib.CategoryTheory.Whiskering`.

- `Sheaf.Paper.ModuleCupCoefficientResolutionMaps`.
- `Sheaf.Paper.ModuleCupCosimplicialAWNaturality`.
- `Sheaf.Paper.ModuleCupCosimplicialFMapSummands`.
- `Sheaf.Paper.ModuleCupGodementCoefficientComplexes`.
- `Sheaf.Paper.ModuleCupGodementCoefficientModels`.
- `Sheaf.Paper.ModuleCupGodementFMapModels`.
- `Sheaf.Paper.ModuleCupGodementFMapSummands`.
- `Sheaf.Paper.ModuleCupPullbackAugmentedPairings`.
- `Sheaf.Paper.ModuleCupPullbackFlasqueComplexes`.
- `Sheaf.Paper.ModuleCupPullbackResolutionMaps`.
- `Sheaf.Paper.ModuleCupResolutionFMap`.

DAG nodes attached to the removed modules:

- `def-pc-cycle-pullback-tower-data-stage3` (`Sheaf.Algebra.Homology.CyclePullbackTower`).
- `def-pc-derived-category` (`Sheaf.AlgebraicGeometry.DerivedCategory`).
- `def-pc-flat-sheaf-modules` (`Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`).
- `def-pc-global-derived-rhom` (`Sheaf.AlgebraicGeometry.GlobalDerivedHom`).
- `def-pc-kflat-complex` (`Sheaf.Algebra.Homology.KFlat`).
- `def-pc-module-kflat-complex` (`WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`).
- `def-pc-ringed-module-skyscraper` (`Sheaf.Topology.RingedModuleSkyscraper`).
- `def-pc-scheme-derived-tensor-structure` (`Sheaf.AlgebraicGeometry.DerivedTensorStructure`).
- `def-pur-derived-internal-hom` (`Sheaf.Algebra.Homology.DerivedInternalHom`).
- `def-pur-hom-complex` (`Sheaf.Algebra.Homology.HomComplex`).
- `def-sc-cech-cup-product` (`Sheaf.Paper.CechCupProduct`).
- `def-sc-module-cohomology-cup-product` (`Sheaf.Paper.ModuleCohomologyCupProduct`).
- `def-sc-module-cup-cochain-pullback-comparison` (`Sheaf.Paper.ModuleCupCochainComparisonSquares`).
- `def-sc-module-cup-realization-complex-data` (`Sheaf.Paper.ModuleCupRealizationComplexData`).
- `def-tower-canonical-comparison-g3` (`Sheaf.Algebra.Homology.CyclePullbackTowerComparison`).
- `lem-pc-bounded-above-flat-kflat-site` (`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`).
- `lem-pc-bounded-above-flat-tensor-acyclic` (`Sheaf.Algebra.Homology.BoundedAboveFlatTensorAcyclic`).
- `lem-pc-bounded-above-flat-tensor-acyclic-degree` (`Sheaf.Algebra.Homology.BoundedAboveFlatTensorAcyclicDegree`).
- `lem-pc-complex-hocolim-colimit` (`Sheaf.Algebra.Homology.TelescopeColimit`).
- `lem-pc-cycle-pullback-tower-comparison-stage3` (`Sheaf.Algebra.Homology.CyclePullbackTowerComparison`).
- `lem-pc-cycle-pullback-tower-laws-stage3` (`Sheaf.Algebra.Homology.CyclePullbackLaws`).
- `lem-pc-derived-category-locally-small` (`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`).
- `lem-pc-flat-augmentation-epicification` (`Sheaf.Algebra.Homology.FlatAugmentationEpicification`).
- `lem-pc-flat-truncation-successor` (`Sheaf.Algebra.Homology.FlatTruncationSuccessor`).
- `lem-pc-flat-truncation-telescope-comparison` (`Sheaf.Algebra.Homology.FlatTruncationTelescopeComparison`).
- `lem-pc-flat-truncation-tower` (`Sheaf.Algebra.Homology.FlatTruncationTower`).
- `lem-pc-functorial-cycle-pullback-construction` (`Sheaf.Algebra.Homology.CyclePullbackResolution`).
- `lem-pc-functorial-cycle-pullback-core-stage3` (`Sheaf.Algebra.Homology.CyclePullbackCore`).
- `lem-pc-functorial-cycle-pullback-lifting-stage3` (`Sheaf.Algebra.Homology.CyclePullbackLifting`).
- `lem-pc-inverse-image-module-functor-exact` (`Sheaf.AlgebraicGeometry.InverseImageModuleFunctor`).
- `lem-pc-inverse-image-tensor-pullback-comparison` (`Sheaf.AlgebraicGeometry.InverseImageTensorPullbackComparison`).
- `lem-pc-kflat-bounded-flat-replacement` (`Sheaf.Algebra.Homology.BoundedFlatReplacement`).
- `lem-pc-kflat-closure` (`Sheaf.Algebra.Homology.KFlatTelescopeClosure`).
- `lem-pc-kflat-cone-direct-sum` (`Sheaf.Algebra.Homology.KFlatClosure`).
- `lem-pc-kflat-extension-of-scalars` (`Sheaf.Algebra.Homology.KFlatModuleBaseChange`).
- `lem-pc-kflat-hocolim-truncations` (`Sheaf.Algebra.Homology.TruncationTelescope`).
- `lem-pc-kflat-pullback-preservation` (`Sheaf.Algebra.Homology.KFlatPullback`).
- `lem-pc-kflat-resolution` (`Sheaf.Algebra.Homology.KFlatResolution`).
- `lem-pc-kflat-stalk-criterion` (`Sheaf.Algebra.Homology.KFlatStalkCriterion`).
- `lem-pc-kflat-tensor-cone-two-out-of-three` (`Sheaf.Algebra.Homology.KFlatTensorConeTwoOutOfThree`).
- `lem-pc-module-filtered-colimits-tensor` (`Sheaf.Algebra.Homology.FilteredColimitsTensor`).
- `lem-pc-module-filtered-colimits-tensor-preserves` (`Sheaf.Algebra.Homology.FilteredColimitsTensorTotal`).
- `lem-pc-point-module-evaluation-equivalence` (`Sheaf.Topology.PointModuleEvaluationEquivalence`).
- `lem-pc-relative-flat-extension` (`Sheaf.Algebra.Homology.RelativeFlatExtension`).
- `lem-pc-ringed-inverse-image-stalk-scalar-transport` (`Sheaf.Algebra.Homology.InverseImageStalkScalarTransport`).
- `lem-pc-ringed-inverse-image-stalk-scalar-transport-beta` (`Sheaf.Algebra.Homology.InverseImageStalkScalarTransportBeta`).
- `lem-pc-ringed-inverse-image-stalk-scalar-transport-naturality` (`Sheaf.Algebra.Homology.InverseImageStalkScalarTransportNaturality`).
- `lem-pc-ringed-space-tensor-pullback-underived` (`Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived`).
- `lem-pc-scheme-module-free-yoneda-iso` (`Sheaf.AlgebraicGeometry.SchemeModuleFreeYonedaIso`).
- `lem-pc-sites-module-sheafification-bilinear-extension` (`Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`).
- `lem-pc-sites-module-sheafification-bilinear-extension-existence` (`Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionExistence`).
- `lem-pc-sites-module-sheafification-bilinear-extension-uniqueness` (`Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionUniqueness`).
- `lem-pc-sites-module-sheafification-tensor` (`Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`).
- `lem-pc-sites-modules-coproduct-flat` (`Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct`).
- `lem-pc-sites-modules-functorial-flat-cover` (`Sheaf.Algebra.Homology.FlatCoverFunctor`).
- `lem-pc-sites-modules-j-shriek-flat` (`Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat`).
- `lem-pc-sites-modules-sheafification-flat` (`Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat`).
- `lem-pc-sites-sheaf-tensor-bilinear-universal` (`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`).
- `lem-pc-skyscraper-complex` (`Sheaf.Topology.SkyscraperComplex`).
- `lem-pc-skyscraper-complex-acyclic` (`Sheaf.Topology.SkyscraperComplexAcyclic`).
- `lem-pc-skyscraper-complex-stalk-recovery` (`Sheaf.Topology.SkyscraperComplexStalk`).
- `lem-pc-source-kflat-module-tensor-model` (`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`).
- `lem-pc-source-module-kflat-resolution` (`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`).
- `lem-pc-stalk-tensor-complex` (`Sheaf.Algebra.Homology.StalkTensorComplex`).
- `lem-pc-stalk-tensor-complex-degrees` (`Sheaf.Algebra.Homology.StalkTensorComplexDegrees`).
- `lem-pc-stalk-tensor-complex-differential` (`Sheaf.Algebra.Homology.StalkTensorComplexDifferential`).
- `lem-pc-telescope-shift-mono` (`Sheaf.Algebra.Homology.TelescopeShiftMono`).
- `lem-pc-tensor-mapping-cone-iso` (`WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`).
- `lem-pc-tensor-pullback-stalk-complex` (`Sheaf.Algebra.Homology.TensorPullbackStalkComplex`).
- `lem-pc-tensor-restrict-extend-module-natural` (`Sheaf.Algebra.Homology.TensorRestrictExtendScalarsModule`).
- `lem-pc-tensor-restrict-extend-scalars` (`Sheaf.Algebra.Homology.TensorRestrictExtendScalars`).
- `lem-pur-acyclic-kflat-tensor-arbitrary` (`Sheaf.Algebra.Homology.AcyclicKFlatTensor`).
- `lem-pur-change-of-rings-acyclic-kflat` (`Sheaf.Algebra.Homology.ChangeOfRingsAcyclicKFlat`).
- `lem-pur-change-of-rings-kflat-quasi-iso` (`Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso`).
- `lem-pur-change-of-rings-tensor-acyclic` (`Sheaf.Algebra.Homology.ChangeOfRingsTensorAcyclic`).
- `lem-pur-change-of-rings-tensor-comparison` (`Sheaf.Algebra.Homology.ChangeOfRingsTensorComparison`).
- `lem-pur-hom-complex-sections-canonical-comparison` (`Sheaf.Algebra.Homology.HomComplexSectionsCanonicalComparison`).
- `lem-pur-hom-complex-sections-cochains` (`Sheaf.Algebra.Homology.HomComplexSectionsCochains`).
- `lem-pur-hom-complex-sections-cochains-comm` (`Sheaf.Algebra.Homology.HomComplexSectionsCochainsComm`).
- `lem-pur-hom-complex-sections-derived-naturality` (`Sheaf.Algebra.Homology.HomComplexSectionsDerivedNaturality`).
- `lem-pur-hom-complex-sections-homotopy-naturality` (`Sheaf.Algebra.Homology.HomComplexSectionsHomotopyNaturality`).
- `lem-pur-hom-complex-sections-quasi-iso` (`Sheaf.Algebra.Homology.HomComplexSectionsQuasiIso`).
- `lem-pur-kinjective-restrict-localized` (`Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`).
- `lem-pur-kinjective-restrict-localized-adjunction` (`Sheaf.Algebra.Homology.LocalizedRestrictionAdjunction`).
- `lem-pur-localized-hom-complex-boundaries` (`Sheaf.Algebra.Homology.LocalizedHomComplexBoundaries`).
- `lem-pur-localized-hom-complex-cycle-lift` (`Sheaf.Algebra.Homology.LocalizedHomComplexCycleLift`).
- `lem-pur-localized-hom-complex-cycles-aux` (`Sheaf.Algebra.Homology.LocalizedHomComplexCycles`).
- `lem-pur-localized-hom-complex-cycles-bijective` (`Sheaf.Algebra.Homology.LocalizedHomComplexCyclesBijective`).
- `lem-pur-localized-hom-complex-cycles-forward` (`Sheaf.Algebra.Homology.LocalizedHomComplexCyclesForward`).
- `lem-pur-localized-hom-complex-homology-aux` (`Sheaf.Algebra.Homology.LocalizedHomComplexHomology`).
- `lem-pur-localized-hom-complex-homotopy` (`Sheaf.Algebra.Homology.LocalizedHomComplexHomotopy`).
- `lem-pur-localized-module-restriction-quasi-iso` (`Sheaf.Algebra.Homology.LocalizedModuleRestrictionQuasiIso`).
- `lem-pur-quasi-iso-of-sections` (`Sheaf.Algebra.Homology.QuasiIsoOfSections`).
- `lem-pur-rhom-into-kinjective-local` (`Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal`).
- `lem-pur-rhom-well-defined` (`Sheaf.Algebra.Homology.QuasiIsoHomComplexMap`).
- `lem-sc-cech-cup-resolution-representatives` (`Sheaf.Paper.CechCupResolutionRepresentatives`).
- `lem-sc-etale-qcoherent-presheaf-functorial` (`Sheaf.AlgebraicGeometry.EtaleTensorSections`).
- `lem-sc-global-sections-lax-monoidal-data` (`Sheaf.Paper.GlobalSectionsLaxMonoidalData`).
- `lem-sc-global-tensor-pullback-derived-data` (`Sheaf.Paper.GlobalTensorPullbackDerivedData`).
- `lem-sc-global-tensor-pullback-kflat` (`Sheaf.Paper.GlobalTensorPullbackKFlat`).
- `lem-sc-global-tensor-pullback-mates-isiso` (`Sheaf.Paper.GlobalTensorPullbackMatesIsIso`).
- `lem-sc-global-tensor-pullback-monoidal-normalization` (`Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization`).
- `lem-sc-global-tensor-pullback-oplax-isiso` (`Sheaf.Paper.GlobalTensorPullbackOplaxIsIso`).
- `lem-sc-global-tensor-pullback-tensor-descent` (`Sheaf.Paper.GlobalTensorPullbackTensorDescent`).
- `lem-sc-global-tensor-pullback-underived-data` (`Sheaf.Paper.GlobalTensorPullbackUnderivedData`).
- `lem-sc-module-cup-adjunction-polygon` (`Sheaf.Paper.ModuleCupAdjunctionPolygon`).
- `lem-sc-module-cup-canonical-hzero-identification` (`Sheaf.Paper.ModuleCupCanonicalHZeroIdentification`).
- `lem-sc-module-cup-cochain-comparison-squares` (`Sheaf.Paper.ModuleCupCochainComparisonSquares`).
- `lem-sc-module-cup-cochain-counit-tensor` (`Sheaf.Paper.ModuleCupCochainCounitTensor`).
- `lem-sc-module-cup-derived-tensor-connectivity` (`Sheaf.Paper.ModuleCupDerivedTensorConnectivity`).
- `lem-sc-module-cup-equal-derived-maps-class` (`Sheaf.Paper.ModuleCupEqualDerivedMapsClass`).
- `lem-sc-module-cup-global-counit-comparison` (`Sheaf.Paper.ModuleCupGlobalCounitComparison`).
- `lem-sc-module-cup-global-tensor-comparison` (`Sheaf.Paper.ModuleCupGlobalTensorComparison`).
- `lem-sc-module-cup-global-tensor-pullback` (`Sheaf.Paper.ModuleCupGlobalTensorPullback`).
- `lem-sc-module-cup-hzero-identification` (`Sheaf.Paper.ModuleCupHZeroIdentification`).
- `lem-sc-module-cup-kinjective-target` (`Sheaf.Paper.ModuleCupKInjectiveTarget`).
- `lem-sc-module-cup-naive-derived-compatibility` (`Sheaf.Paper.ModuleCupNaiveDerivedCompatibility`).
- `lem-sc-module-cup-naive-map-chain` (`Sheaf.Paper.ModuleCupNaiveMap`).
- `lem-sc-module-cup-pairing-exists` (`Sheaf.Paper.ModuleCupPairingExists`).
- `lem-sc-module-cup-polygon-calculation` (`Sheaf.Paper.ModuleCupAdjunctionCalculation`).
- `lem-sc-module-cup-realization-evaluation` (`Sheaf.Paper.ModuleCupRealizationEvaluation`).
- `lem-sc-module-cup-resolution-augmentation` (`Sheaf.Paper.ModuleCupResolutionAugmentation`).
- `lem-sc-module-cup-resolution-chain-equation` (`Sheaf.Paper.ModuleCupComponentChainEquation`).
- `lem-sc-module-cup-resolution-components` (`Sheaf.Paper.ModuleCupResolutionExistence`).
- `lem-sc-module-cup-resolution-existence` (`Sheaf.Paper.ModuleCupResolutionExistence`).
- `lem-sc-module-cup-resolution-invariance` (`Sheaf.Paper.ModuleCupResolutionInvariance`).
- `lem-sc-module-cup-resolution-realization` (`Sheaf.Paper.ModuleCupResolutionRealization`).
- `lem-sc-module-cup-resolution-section-map` (`Sheaf.Paper.ModuleCupComponentSectionMap`).
- `lem-sc-modulecat-cocontinuous-generator` (`Sheaf.Algebra.Category.ModuleCat.CocontinuousGenerator`).
- `lem-sc-picard-cech-cup-pullback-compat` (`Sheaf.Paper.CechCupPullbackCompat`).
- `lem-sc-picard-external-cech-cup-bidegree` (`Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree`).
- `lem-sc-point-inverse-evaluation-kflat` (`Sheaf.Paper.PointInverseEvaluationKFlat`).
- `lem-sc-source-kflat-tensor-left-triangulated` (`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`).
- `lem-sc-source-tor-amplitude-flat-model` (`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`).
- `lem-sc-source-tor-amplitude-lower-tensor-bound` (`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`).
- `lem-sc-source-tor-amplitude-upper-tensor-bound` (`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`).
- `lem-weil-pbc-flat-coproduct` (`WeilConjectures.CategoryTheory.Abelian.Flat.Basic`).
- `lem-weil-pbc-module-cohomology-fmap-basic-degree-zero` (`Sheaf.AlgebraicGeometry.BasicPropertiesDegreeZero`).
- `lem-weil-pbc-module-cohomology-fmap-basic-identity` (`Sheaf.AlgebraicGeometry.BasicPropertiesIdentity`).
- `lem-weil-pbc-module-cohomology-fmap-basic-linearity` (`Sheaf.AlgebraicGeometry.BasicPropertiesLinearity`).
- `lem-weil-pbc-module-cohomology-fmap-basic-properties` (`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties`).
- `lem-weil-pbc-module-cohomology-fmap-basic-restriction` (`Sheaf.AlgebraicGeometry.BasicPropertiesRestriction`).
- `lem-weil-pbc-module-cohomology-fmap-comp-data` (`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapCompData`).
- `lem-weil-pbc-module-cohomology-fmap-comparison` (`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapComparison`).
- `lem-weil-pbc-module-cohomology-fmap-data-linearity` (`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapDataLinearity`).
- `lem-weil-pbc-module-cohomology-fmap-functorial` (`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`).
- `lem-weil-pbc-module-cohomology-fmap-identity-resolution-homology` (`Sheaf.AlgebraicGeometry.IdentityResolutionHomology`).
- `lem-weil-pbc-module-cohomology-fmap-semilinear-lift` (`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapSemilinear`).
- `lem-weil-pbc-module-cohomology-fmap-target-iso-naturality` (`Sheaf.AlgebraicGeometry.RestrictionNaturality`).
- `lem-weil-pbc-module-cohomology-fmap-zero-augmentation` (`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapZeroAugmentation`).
- `lem-weil-pbc-right-adjoint-preserves-kinjective` (`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`).
- `lem-weil-pbc-sheaf-flat-separator` (`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`).
- `lem-weil-pbc-sheaf-tensor-closed` (`WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`).
- `new-localized-restriction-extension-exists` (`Sheaf.Algebra.Homology.LocalizedRestrictionExtensionExists`).
- `new-tower-comparison-first` (`Sheaf.Algebra.Homology.CyclePullbackTowerComparison`).
- `new-tower-comparison-second` (`Sheaf.Algebra.Homology.CyclePullbackTowerComparison`).

- `lem-sc-module-cup-coefficient-resolution-maps` (`Sheaf.Paper.ModuleCupCoefficientResolutionMaps`).
- `lem-sc-module-cup-cosimplicial-aw-natural` (`Sheaf.Paper.ModuleCupCosimplicialAWNaturality`).
- `lem-sc-module-cup-godement-coefficient-complexes` (`Sheaf.Paper.ModuleCupGodementCoefficientComplexes`).
- `lem-sc-module-cup-godement-coefficient-models` (`Sheaf.Paper.ModuleCupGodementCoefficientModels`).
- `lem-sc-module-cup-godement-fmap-summands` (`Sheaf.Paper.ModuleCupGodementFMapSummands`).
- `lem-sc-module-cup-pullback-augmented-pairings` (`Sheaf.Paper.ModuleCupPullbackAugmentedPairings`).
- `lem-sc-module-cup-pullback-flasque-complexes` (`Sheaf.Paper.ModuleCupPullbackFlasqueComplexes`).
- `lem-sc-module-cup-pullback-resolution-maps` (`Sheaf.Paper.ModuleCupPullbackResolutionMaps`).
- `lem-sc-module-cup-resolution-fmap` (`Sheaf.Paper.ModuleCupResolutionFMap`).
- `new-module-cup-cosimplicial-fmap-summands` (`Sheaf.Paper.ModuleCupCosimplicialFMapSummands`).
- `new-module-cup-godement-fmap-models` (`Sheaf.Paper.ModuleCupGodementFMapModels`).

## Where the brief, the DAG or earlier work was wrong

The full planned argument was already proved by `picardModuleCech_externalPairing`.
Its expanded predicates conceal the duplicate statement; reusing it closes the chain
without adding another sorry. The assignment snapshot also became stale when the
P3 delivery was rolled back during this session, producing the first dry-run's new
module/node errors. The restoration metadata and change record address that change.

The P3 return identifies a real non-module batch probe collision in the heavy cup
import chain. The restoration follows E3's lightweight expanded-signature repair.
No mathematical error in the assigned theorem was found; degree zero, empty covers
and zero coefficients retain exactly the original hypotheses and conclusion.

## New nodes

`lem-sc-picard-module-cech-external-cup` is restored because the fetched base removed
it. It records the same self-contained mathematical statement and unchanged source,
chapter and unit, the definitionally equal expanded Lean signature, W3 restoration
metadata, fresh recorded Mathlib searches and the actual single-theorem proof route.
It carries no new or remaining hole. No further node is introduced.

Change record: `coord/changes/picard-module-cech-external-cup-restore.md`.

## Second reading by W3

1. Signature and visible changes: PASS. The repository version of this module and
   node is absent after the rollback, as the change record reports. Diffed the
   preserved assignment signature against the delivered declaration: only hcup and
   hl are expanded. An independent scratch proof establishes equality of the entire
   old and new dependent theorem types by rfl, and both front/back function
   equalities by rfl. Thus all binders and the conclusion are retained, with
   definitionally equal types. No target or definition changes. A source search
   confirms there is no existing consumer of the withdrawn declaration.
2. Proof and axioms: PASS. Compiled the delivered module without errors or warnings
   (7.1 seconds). Read its exact application of the existing pairing theorem and
   that theorem's refinement/cup proof. The file has no sorry, forbidden declaration,
   new definition or arbitrary chosen witness. The existing adjunction choice in
   the hypothesis has a prescribed sectionwise unit determining all values used.
   An independent scratch copy printed only propext, Classical.choice, Quot.sound
   and sorryAx; the latter comes from already open imported obligations. One local
   hole is closed, none added; this does not close the target's axiom obligations.
3. Split-off statements: PASS, none. The restored node describes the assigned
   theorem, not an additional unproved lemma. Checked degree zero, zero coefficients
   and empty cover indices: all retain the original hypotheses; an empty cover
   forces the corresponding scheme empty. Repeated a Mathlib search with different
   wording (external pairing / Cech comparison cup, zero hits) and searched the
   project library; the already proved externalPairing is the direct reuse found.
4. Route, imports and pruning: PASS after report correction. Each public import
   supplies symbols in the expanded signature; externalPairing is proof-only.
   The reused theorem carries the same product-cover refinements, three homology
   transports and ordinary cup comparison. Read dag/units/sk-prop-av-cube.json: its
   existing realized arrays are empty and unchanged; this auxiliary calculation
   replaces no step of the unit or chapter. Recomputed the project import graph: 262
   modules removed relative to the recorded assignment imports, rather than the
   stale 251. Added the eleven missing modules and their attached node IDs. These
   are local closure removals, not a claim of whole-target ledger progress.
5. DAG agreement: PASS after wording correction. The node's Lean statement matches
   the delivered signature byte for byte. Its only proof dependency is the existing
   external-pairing node, exactly as used by Lean; proof_origin names that reuse.
   Source, chapter, unit, restored-node metadata and the three required search kinds
   are present. Corrected the proof-step wording to say the expanded signature is
   definitionally equal, rather than implying its text is unchanged.

Second reading changed report pruning/dependency accounting and DAG proof wording.
The Lean proof, declaration, imports and existing docstring needed no repair.
Independent equality/axiom probes remain in scratchpad only and are not delivered.
