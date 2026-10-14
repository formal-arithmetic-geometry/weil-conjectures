## What changed

Proved `AlgebraicGeometry.exists_affineCoordinateComparisonFamily` with its original
statement and universes. Construct the canonical comparison as the adjunction mate
of the affine global-sections square, lift it degreewise and through the homotopy
quotient, and invert the precise counit selected by `perfectHomComposition` on K-flat
models. The underived mate-pasting equation and the fixed derived counit equation
prove the cocycle. Conjugating by the supplied chart isomorphisms proves the displayed
comparison for the original `H` functors. Restricting this natural comparison to the
full induced category preserves all cross-label morphisms, and evaluating the same
one-model cocycle at M and N proves both Boolean components.

The three existing definitions `AffineComparisonCoordinate`, `AffineComparisonKFlat`
and `AffineCoordinateComparisonFamily` move verbatim into
`Sheaf.AlgebraicGeometry.AffineCoordinateComparisonData`, publicly re-exported by the
item. This prevents a circular import of the data and its comparison proof. Both
original theorem signatures are unchanged. The already proved
`exists_affineCoordinateComparisonTransportFamily` and its private categorical
transport proof are retained. No existing module outside the item is adapted.

Nine new modules provide the data, concrete chart/K-flat API, fixed counit API,
adjunction-square pasting, inverse-counit/naturality calculus, underived comparison,
derived comparison, family component formula and one-model cocycle. Every new module
is fully proved, with no new `sorry`. Their nine DAG nodes and the parent proof route
are recorded. The unit's realized statement/steps are unchanged.

All ten modules compile cleanly with `lcompile.py --all`; the definitions and theorem
signatures were also compared with the original text. The termwise comparison is
factored through application of composite functors rather than repeatedly unfolding
the adjunction mate. This keeps each file within the prescribed 60-second limit.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_affineCoordinateComparisonFamily`
(node `lem-pc-affine-coordinate-comparison-coherence`). The existing theorem
`AlgebraicGeometry.exists_affineCoordinateComparisonTransportFamily` remains proved.

Original holes closed: 1 of 1. New holes added: 0. Holes left in the item or any new
module of this delivery: none. This is a proof from the existing library declarations,
not a decomposition into new unproved statements. In particular, both the canonical
underived comparison coherence and the inverse-counit composition calculation are
proved here rather than left to another worker.

The following public helper theorems are also proved:

- `AlgebraicGeometry.affineCoordinateChartObjectComparison_cocycle`.
- `AlgebraicGeometry.exists_affineCoordinateComparisonFamilyBase`.
- `AlgebraicGeometry.affineCoordinateObjectDerivedComparison_naturality`.
- `AlgebraicGeometry.affineCoordinateChartObjectComparison_naturality`.
- `AlgebraicGeometry.affineCoordinateComplex_isKFlat`.
- `AlgebraicGeometry.affineCoordinateGammaComparison_comp`.
- `AlgebraicGeometry.affineCoordinateTensorComparison_comp`.
- `AlgebraicGeometry.affineCoordinateComplexComparison_hom_f`.
- `AlgebraicGeometry.affineCoordinateHomotopy_map`.
- `AlgebraicGeometry.affineCoordinateHomotopyComparison_hom_app`.
- `AlgebraicGeometry.affineCoordinateHomotopyComparison_comp`.
- `AlgebraicGeometry.perfectHomTensorCounit_isIso`.
- `AlgebraicGeometry.perfectHomTensorHomotopy_map`.
- `AlgebraicGeometry.perfectHomTensorHomotopyComp_hom_app`.
- `AlgebraicGeometry.perfectHomTensorCounit_comp`.
- `CategoryTheory.adjunctionSquareComposition`.
- `CategoryTheory.counitComparisonComposition`.
- `CategoryTheory.conjugateComparisonComposition`.
- `CategoryTheory.conjugateComparisonNaturality`.
- `CategoryTheory.inverseCounitNaturality`.
- `CategoryTheory.inverseCounitModelNaturality`.

The remaining imported project obligations are the existing declarations behind the
K-flat tilde/pullback and derived-pullback/composition APIs; this delivery neither adds
holes to them nor claims that those independent dependencies have been completed.

## No longer needed

Removed the item's direct proof imports
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`,
`Sheaf.AlgebraicGeometry.AffineSquareKFlatModelIso`, and
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`.
The first two modules and their nodes
`lem-pc-affine-derived-pullback-tensor-tilde` and
`lem-pc-affine-square-kflat-model-iso` are absent from the new proof/import route.
`DerivedPullbackComposition` remains needed through `PerfectHomTransport` and the
fixed counit API; its node is not pruned. Scalar-extension K-flatness likewise remains
needed and is not pruned.

The original public imports now live in the data module and are publicly re-exported
by the item. Their duplicate direct imports were removed; this does not remove their
public API. Removed trial helpers `perfectHomCochainCounit`,
`perfectHomCochainCounit_isIso`, and `affineCoordinateComplex_map_f`, and the unused
trial import `TensorPullbackCompositionIso`. The derived comparison no longer repeats
the tensor module's public counit import. The cocycle imports the derived comparison
directly, without depending on the family-assembly module.

Discarded the inherited, undelivered split modules
`Sheaf.AlgebraicGeometry.AffineCoordinateComparisonFamilyTrue` and
`Sheaf.AlgebraicGeometry.AffineCoordinateComparisonFamilyFalse`, and do not use their
nodes `new-affine-coordinate-comparison-family-true` or
`new-affine-coordinate-comparison-family-false`. They have no Lean source in the
read-only repository, so no landed Lean module is withdrawn. No new split-off remains.

Comparing this item's original and delivered transitive imports removes 263 local
project modules from this item's closure (693 before, 439 after, including the nine
new modules). The complete list below records each module and any associated DAG
nodes. This is pruning of this item's route; other targets may independently need
some entries. No blueprint unit statement or realized proof step is removed.

| Module removed from this item's import closure | Associated DAG nodes |
| --- | --- |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat` | `lem-pc-sites-modules-j-shriek-flat` |
| `Sheaf.Algebra.Homology.KFlatTensorProduct` | `lem-pc-kflat-tensor-product` |
| `Sheaf.Algebra.Homology.KernelShiftedMappingCone` | `lem-weil-degreewise-epi-kernel-cocone-qis` |
| `Sheaf.Algebra.Homology.LowerTruncationStepTriangle` | `lem-pc-derived-lower-truncation-step-triangle` |
| `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact` | `lem-sc-derived-open-restriction-adjunction-exact` |
| `Sheaf.Algebra.Homology.RoosComparisonHomotopies` | `lem-weil-roos-comparison-homotopies` |
| `Sheaf.Algebra.Homology.RoosComparisonHomotopyRetract` | `lem-weil-roos-comparison-homotopy-retract` |
| `Sheaf.Algebra.Homology.RoosComparisonMaps` | `lem-weil-roos-comparison-maps` |
| `Sheaf.Algebra.Homology.RoosComplex` | `lem-weil-derived-limit-roos-complex` |
| `Sheaf.Algebra.Homology.RoosSplitComparison` | `lem-weil-roos-split-comparison` |
| `Sheaf.Algebra.Homology.TowerEvaluationKInjective` | `lem-weil-tower-evaluation-kinjective` |
| `Sheaf.Algebra.Homology.TowerSplitComplexReplacement` | `lem-weil-tower-split-complex-replacement` |
| `Sheaf.AlgebraicGeometry.AffineDerivedCounitHomologyFactorization` | `new-affine-derived-counit-homology-factorization` |
| `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` | `lem-pc-affine-derived-pullback-tensor-tilde` |
| `Sheaf.AlgebraicGeometry.AffineDerivedSectionsHomologyComparison` | `lem-pc-affine-derived-sections-homology-comparison` |
| `Sheaf.AlgebraicGeometry.AffineDerivedSectionsTruncatedBottom` | `new-affine-derived-sections-truncated-bottom` |
| `Sheaf.AlgebraicGeometry.AffineDerivedSectionsTruncationIso` | `new-affine-derived-sections-truncation-iso` |
| `Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison` | `new-affine-derived-tilde-homology-comparison` |
| `Sheaf.AlgebraicGeometry.AffineDerivedUnitHomologyIsIso` | `new-affine-derived-unit-homology-isIso` |
| `Sheaf.AlgebraicGeometry.AffineDerivedUnitIsomorphism` | `lem-pc-affine-derived-unit-isomorphism` |
| `Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing` | `pqf-lem-affine-vanishing` |
| `Sheaf.AlgebraicGeometry.AffineQCohDerivedAdjunctionConstruction` | `new-affine-qcoh-derived-adjunction-construction` |
| `Sheaf.AlgebraicGeometry.AffineQCohDerivedAdjunctionUnitCounit` | `new-affine-qcoh-derived-adjunction-unit-counit` |
| `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence` | `lem-pc-affine-qcoh-derived-equivalence` |
| `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore` | `new-affine-qcoh-derived-equivalence-core` |
| `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceShift` | `new-affine-qcoh-derived-equivalence-shift` |
| `Sheaf.AlgebraicGeometry.AffineQCohDerivedTildeTriangulated` | `new-affine-qcoh-derived-tilde-triangulated` |
| `Sheaf.AlgebraicGeometry.AffineSquareKFlatModelIso` | `lem-pc-affine-square-kflat-model-iso` |
| `Sheaf.AlgebraicGeometry.AffineTildeDerivedSectionsUnitIsIso` | `new-affine-tilde-derived-sections-unit-isIso` |
| `Sheaf.AlgebraicGeometry.AffineTildeTotalTensor` | `lem-pc-affine-tilde-total-tensor` |
| `Sheaf.AlgebraicGeometry.Coherent` | `pqf-def-coherent` |
| `Sheaf.AlgebraicGeometry.DerivedFunctorTruncationStabilization` | `lem-pc-derived-functor-truncation-stabilization` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel` | `lem-pc-derived-pullback-kflat-tensor-model` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent` | `lem-pc-derived-pullback-tensor-comparison-descent` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct` | `lem-pc-derived-pullback-tensor-product` |
| `Sheaf.AlgebraicGeometry.DerivedTensorStructure` | `def-pc-scheme-derived-tensor-structure` |
| `Sheaf.AlgebraicGeometry.KFlatBifunctorIsoDescent` | `lem-pc-kflat-bifunctor-iso-descent` |
| `Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison` | `lem-pc-kflat-derived-tensor-comparison` |
| `Sheaf.AlgebraicGeometry.MLSetsTowerLimitNonempty` | `lem-weil-pbc-ml-sets-tower-limit-nonempty` |
| `Sheaf.AlgebraicGeometry.ModuleAbelianZariskiCohomology` | No attached node |
| `Sheaf.AlgebraicGeometry.ModulePullbackTensor` | `lem-weil-pbc-module-pullback-tensor` |
| `Sheaf.AlgebraicGeometry.Modules.AffineTildeTensor` | `lem-weil-pbc-affine-tilde-tensor` |
| `Sheaf.AlgebraicGeometry.Modules.AffineTildeTensorStalk` | `lem-weil-pbc-affine-tilde-tensor-stalk-bijective` |
| `Sheaf.AlgebraicGeometry.Modules.InverseImageStalkScalarTransport` | `lem-pc-inverse-image-stalk-scalar-transport` |
| `Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk` | `lem-weil-pbc-module-stalk-pullback` |
| `Sheaf.AlgebraicGeometry.Modules.TensorPullbackTensorIsIso` | `lem-weil-pbc-module-pullback-tensor-iso-criterion` |
| `Sheaf.AlgebraicGeometry.OpenModuleCohomologyComparison` | `lem-pqf-open-module-cohomology-comparison` |
| `Sheaf.AlgebraicGeometry.QCohTruncationDerivedLimit` | `lem-pc-qcoh-truncation-derived-limit` |
| `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage` | `def-pc-ringed-spaces-derived-direct-image` |
| `Sheaf.AlgebraicGeometry.RingedSpaceSheafificationCohomology` | `lem-pc-ringed-space-sheafification-cohomology` |
| `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage` | `def-pc-derived-direct-image` |
| `Sheaf.AlgebraicGeometry.SchemeModuleFreeYonedaIso` | `lem-pc-scheme-module-free-yoneda-iso` |
| `Sheaf.AlgebraicGeometry.TensorPullbackTilde` | `lem-weil-pbc-tilde-pullback-base-change` |
| `Sheaf.AlgebraicGeometry.TruncationDerivedLimit` | `lem-pc-ringed-space-truncation-derived-limit` |
| `Sheaf.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound` | `lem-pc-unbounded-derived-functor-cohomological-bound` |
| `Sheaf.AlgebraicTopology.SetCechNerveFreeResolution` | `lem-weil-pbc-set-cech-nerve-free-resolution` |
| `Sheaf.CategoryTheory.Abelian.ExtEpiEffacement` | `lem-sc-ext-epi-effacement` |
| `Sheaf.CategoryTheory.Abelian.HorseshoeDefectFactorization` | `lem-weil-pbc-horseshoe-defect-factorization` |
| `Sheaf.CategoryTheory.Abelian.HorseshoeDegreewiseMap` | `lem-weil-pbc-horseshoe-degreewise-map` |
| `Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor` | `lem-weil-pbc-horseshoe-delta-functor` |
| `Sheaf.CategoryTheory.Abelian.HorseshoeHomotopyCorrection` | `lem-weil-pbc-horseshoe-homotopy-correction` |
| `Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLift` | `lem-weil-pbc-horseshoe-morphism-lift`, `lem-weil-pbc-horseshoe-preliminary-data`, `lem-weil-pbc-horseshoe-correction` |
| `Sheaf.CategoryTheory.Abelian.HorseshoePrescribedResolutions` | `lem-sp-horseshoe-prescribed-resolutions` |
| `Sheaf.CategoryTheory.Abelian.HorseshoePrescribedRows` | `lem-sp-horseshoe-prescribed-row-construction` |
| `Sheaf.CategoryTheory.Abelian.HorseshoeResolutions` | `lem-weil-pbc-injective-resolution-ses` |
| `Sheaf.CategoryTheory.DeltaFunctor` | `def-weil-pbc-delta-functor` |
| `Sheaf.CategoryTheory.DerivedLimitEventuallyIso` | `lem-pc-derived-limit-eventually-iso` |
| `Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups` | `lem-pc-tower-enough-injectives`, `lem-pc-derived-limit-roos-abelian-groups` |
| `Sheaf.CategoryTheory.EffaceableDeltaFunctorSuccessor` | `lem-weil-pbc-effaceable-delta-functor-successor` |
| `Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal` | `lem-weil-pbc-effaceable-delta-functor-universal` |
| `Sheaf.CategoryTheory.EffacingSequenceComparison` | `lem-weil-pbc-effacing-sequence-comparison` |
| `Sheaf.CategoryTheory.EffacingSequencePushout` | `lem-weil-pbc-effacing-sequence-pushout` |
| `Sheaf.CategoryTheory.InjectiveModulePresheaf` | `lem-weil-pbc-ringed-site-injective-module-injective-presheaf` |
| `Sheaf.CategoryTheory.InjectiveSplitTower` | `lem-pc-injective-split-tower-injective` |
| `Sheaf.CategoryTheory.InjectiveSplitTowerExtension` | `lem-pc-injective-split-tower-extension` |
| `Sheaf.CategoryTheory.InjectiveTowerEmbedding` | `lem-pc-tower-injective-embedding` |
| `Sheaf.CategoryTheory.Limits.TowerTransitionEndomorphism` | `def-weil-tower-transition-endomorphism` |
| `Sheaf.CategoryTheory.MittagLefflerLimitExact` | `lem-weil-pbc-mittag-leffler-limit-exact` |
| `Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso` | `lem-weil-pbc-derived-functor-truncation-iso`, `lem-weil-pbc-derived-functor-truncation-iso-epi`, `lem-weil-pbc-derived-functor-truncation-iso-mono` |
| `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor` | `lem-weil-pbc-right-derived-universal-delta-functor` |
| `Sheaf.CategoryTheory.RoosAcyclicResolution` | `lem-pc-roos-functorial-acyclic-resolution` |
| `Sheaf.CategoryTheory.RoosFinitePrefixLimits` | `lem-pc-roos-finite-prefix-limits` |
| `Sheaf.CategoryTheory.RoosFinitePrefixes` | `lem-pc-roos-finite-prefix-construction` |
| `Sheaf.CategoryTheory.RoosPrefixAcyclic` | `lem-pc-roos-prefix-acyclic` |
| `Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation` | `new-sheaf-cohomology-derived-evaluation` |
| `Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic` | `lem-sc-injective-module-abelian-acyclic-zariski` |
| `Sheaf.CategoryTheory.Sites.InjectivePresheafModuleNerveAcyclic` | `lem-sc-injective-presheaf-module-nerve-acyclic` |
| `Sheaf.CategoryTheory.Sites.PresheafCechComplex` | `def-sc-presheaf-cech-complex` |
| `Sheaf.CategoryTheory.Sites.PresheafCechExtEdgeInjective` | `lem-sc-presheaf-cech-ext-edge-injective` |
| `Sheaf.CategoryTheory.Sites.PresheafCechExtEdgeKernel` | `lem-sc-presheaf-cech-ext-edge-kernel` |
| `Sheaf.CategoryTheory.Sites.PresheafCechSheafAugmentationExact` | `lem-sc-presheaf-cech-sheaf-augmentation-exact` |
| `Sheaf.CategoryTheory.Sites.PresheafCechSheafHomComparison` | `lem-sc-presheaf-cech-sheaf-hom-comparison` |
| `Sheaf.CategoryTheory.Sites.PresheafCechSheafPositiveExact` | `lem-sc-presheaf-cech-sheaf-positive-exact` |
| `Sheaf.CategoryTheory.Sites.PresheafCechSheafResolution` | `lem-sc-presheaf-cech-sheaf-resolution` |
| `Sheaf.CategoryTheory.Sites.PresheafCechVanishingCriterion` | `lem-sc-presheaf-cech-vanishing-criterion` |
| `Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling` | `lem-sc-presheaf-free-ext-local-killing-witness`, `lem-sc-presheaf-free-ext-local-killing` |
| `Sheaf.CategoryTheory.Sites.PresheafFreeNerveComparison` | `lem-sc-presheaf-free-nerve-comparison` |
| `Sheaf.CategoryTheory.Sites.PresheafFreeNerveExact` | `lem-sc-presheaf-free-nerve-exact-eval`, `lem-sc-presheaf-free-nerve-exact-eval-glue`, `lem-sc-presheaf-free-nerve-exact` |
| `Sheaf.CategoryTheory.TowerSplitEnvelope` | `lem-weil-tower-split-envelope` |
| `Sheaf.CategoryTheory.Triangulated.DerivedCountableProductsCore` | `lem-weil-derived-countable-products-core` |
| `Sheaf.CategoryTheory.Triangulated.DerivedCountableProductsExistence` | `lem-weil-derived-countable-products-existence` |
| `Sheaf.CategoryTheory.Triangulated.DerivedCountableProductsProperties` | `lem-weil-derived-countable-products-properties` |
| `Sheaf.CategoryTheory.Triangulated.DerivedFunctorDerivedLimit` | `lem-pc-derived-functor-commutes-derived-limit` |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimit` | `def-weil-derived-limit` |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence` | `lem-weil-derived-limit-existence` |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts` | `lem-weil-derived-limit-products-core` |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitTower` | `lem-weil-derived-limit-tower-core` |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerCone` | `lem-weil-derived-limit-tower-core-cone` |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerProperty` | `lem-weil-derived-limit-tower-core-property` |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerRoosTriangle` | `lem-weil-derived-limit-tower-roos-triangle` |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerTriangle` | `lem-weil-derived-limit-tower-core-property-triangle` |
| `Sheaf.CategoryTheory.Triangulated.MilnorBoundaryFactorization` | `lem-pc-milnor-boundary-factorization` |
| `Sheaf.CategoryTheory.Triangulated.MilnorProjectionFactorization` | `lem-pc-milnor-projection-factorization` |
| `Sheaf.CategoryTheory.Triangulated.MilnorSequence` | `lem-pc-derived-limit-milnor-sequence` |
| `Sheaf.CategoryTheory.Triangulated.RightDerivedFunctorCountableProducts` | `lem-pc-right-derived-functor-countable-products` |
| `Sheaf.CategoryTheory.Triangulated.RingedSpaceDerivedProducts` | `lem-pc-ringed-space-derived-products` |
| `Sheaf.Paper.PQFCohomology` | `pqf-def-cohomology` |
| `Sheaf.Topology.CohomologyPresheafDerivedSectionsEvaluation` | `lem-pc-cohomology-presheaf-derived-sections-evaluation` |
| `Sheaf.Topology.DerivedLimitStalkInjective` | `lem-pc-ringed-space-derived-limit-stalk-injective` |
| `Sheaf.Topology.InverseImageStalk` | `lem-weil-pbc-topological-inverse-image-stalk` |
| `Sheaf.Topology.OpenModuleCohomology` | `def-sc-open-module-cohomology` |
| `Sheaf.Topology.OpenModuleDerivedSections` | `def-pc-open-module-derived-sections` |
| `Sheaf.Topology.PointwiseTruncationLimit` | `lem-pc-ringed-space-pointwise-truncation-limit` |
| `Sheaf.Topology.PointwiseTruncationLimitExists` | `lem-pc-ringed-space-pointwise-truncation-limit-exists` |
| `Sheaf.Topology.PointwiseTruncationLimitIsIso` | `lem-pc-ringed-space-pointwise-truncation-limit-isIso` |
| `Sheaf.Topology.PointwiseTruncationOpenStabilization` | `lem-pc-pointwise-truncation-open-stabilization` |
| `Sheaf.Topology.RestrictInjectiveResolution` | `lem-sc-ringed-space-restrict-injective-resolution` |
| `Sheaf.Topology.RingedSpaceModuleCohomology` | `def-sc-sheaf-cohomology-functor`, `def-sc-ringed-space-module-cohomology` |
| `Sheaf.Topology.RingedSpaceModuleEnoughInjectives` | `lem-sc-ringed-space-module-sheaves-enough-injectives` |
| `Sheaf.Topology.RingedSpaceRGammaDerivedLimit` | `lem-pc-ringed-space-rgamma-derived-limit` |
| `WeilConjectures.Algebra.Homology.BifunctorLinear` | No attached node |
| `WeilConjectures.Algebra.Homology.HomotopyCategory.Braided` | No attached node |
| `WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure` | No attached node |
| `WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom` | No attached node |
| `WeilConjectures.Algebra.Homology.HomotopyCategory.Products` | No attached node |
| `WeilConjectures.Algebra.Homology.InternalHom` | No attached node |
| `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech` | `lem-pc-affine-cech-complex`, `lem-pc-affine-vanishing` |
| `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic` | `lem-pc-right-acyclic-of-epi-map-g`, `def-sp-acyclic`, `lem-weil-pbc-leray-acyclicity-quasi-iso` |
| `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence` | `lemma-weil-pbc-leray-acyclicity` |
| `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory` | No attached node |
| `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed` | No attached node |
| `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift` | `lem-sc-source-kflat-tensor-left-triangulated` |
| `WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage` | No attached node |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction` | No attached node |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` | `lem-weil-pbc-right-adjoint-preserves-kinjective` |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs` | No attached node |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective` | No attached node |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory` | No attached node |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction` | `prop-weil-pbc-derived-inverse-image-adjunction` |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic` | No attached node |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp` | No attached node |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility` | `src-right-derived-functor-plus-compatibility` |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology` | `src-right-derived-functor-plus-acyclic-unit` |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle` | `lem-sp-derived-functor-single-identification` |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated` | `lem-pc-right-derived-functor-triangulated` |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Coefficients` | No attached node |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize` | No attached node |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory` | `lem-pc-derived-category-locally-small` |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify` | No attached node |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs` | No attached node |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution` | `lem-weil-pbc-sheaf-flat-separator` |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits` | No attached node |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf` | `lem-weil-pbc-sheaf-tensor-closed` |
| `WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive` | No attached node |
| `WeilConjectures.CategoryTheory.Monoidal.DerivedBraided` | No attached node |
| `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory` | No attached node |
| `WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory` | No attached node |
| `WeilConjectures.CategoryTheory.Sites.TransfinitePlus` | No attached node |
| `WeilConjectures.CategoryTheory.Sites.TransfinitePlusSheaf` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.Bifunctor` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.BifunctorCommShift` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.BifunctorShift` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Acyclic` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.DegreewiseSplit` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Devissage` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.MonoidalTriangulated` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.PreservesQuasiIso` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Pretriangulated` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.ShiftSequence` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplex` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.Monoidal` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.ObjectProperty` | No attached node |
| `WeilConjectures.FromJoel.Algebra.Homology.Single` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.CurryingThree` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerived` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedBifunctorComp` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedFour` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedThree` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedTrifunctorComp` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedTwo` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Quadrifunctor` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.GuitartExact.Basic` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.Composition` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Derives` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesFour` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesThree` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Monoidal` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Product` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Derived` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat` | `def-pc-module-kflat-complex` |
| `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Pentagon` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.Retract` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.QuotientThree` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.QuotientTwo` | No attached node |
| `WeilConjectures.FromJoel.CategoryTheory.Triangulated.HomologicalFunctor` | No attached node |
| `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB` | No attached node |
| `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.FilteredColimits` | No attached node |
| `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic` | No attached node |
| `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty` | No attached node |
| `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus` | `lem-weil-pbc-derived-functor-negative-vanishing`, `lem-weil-pbc-derived-direct-image-triangulated` |
| `WeilConjectures.Mathlib.Algebra.Homology.Embedding.Extend` | No attached node |
| `WeilConjectures.Mathlib.Algebra.Homology.HomologySequence` | No attached node |
| `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.HomComplex` | No attached node |
| `WeilConjectures.Mathlib.Algebra.Homology.Monoidal` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Limits` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Comma.CardinalArrow` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.EssentialImage` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Adjunction` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Generator.StrongGenerator` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Limits.FunctorCategory.Basic` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Localization.Bousfield` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Linear` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Orthogonal` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves` | `lem-sp-right-adjoint-preserves-injectives` |
| `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Resolution` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Presentable.Limits` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Shift.CommShiftTwo` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Shift.Localization` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.CompatiblePlus` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Equivalence` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Grothendieck` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.LeftExact` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Localization` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Plus` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.SmallObject.TransfiniteIteration` | No attached node |
| `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor` | `lem-weil-pbc-commshift-nattrans-triangle-morphism` |
| `WeilConjectures.Topology.Sheaves.Cech` | `lem-pc-topological-injective-cech-positive-exact` |
| `WeilConjectures.Topology.Sheaves.CechCriterion` | `lem-pc-topological-ses-cech-sections-surjective` |

## Where the brief, the DAG or earlier work was wrong

The inherited true-label split restated nearly the complete construction and did not
identify a canonical family. The proposed false-label transfer was not a valid step:
`STATEMENT-DISPUTED: coherence at the true label of an arbitrary two-model natural
family does not force coherence at its false label.` When M is zero and N is nonzero,
the cross maps are zero and naturality imposes no relation between the two component
automorphisms. Altering the false component by a nontrivial automorphism leaves the
true component unconstrained by that change and can break its composition law. The
original theorem needs a single canonical construction, natural in every model; the
new proof builds it and applies the same one-model cocycle to each label.

The original route through the full affine derived equivalence and a separately
chosen affine-square model comparison was longer than necessary. The supplied chart
identifications already give the concrete localized model. The global-sections
comparison is explicit and composes on underlying sections; its pinned adjunction mate
provides the required coherence without rebuilding the affine derived equivalence.
The original target and all its supplied coordinate data are unchanged.

The LeanSearch service returned Internal Server Error; the real query and failure
are recorded, with LeanFinder, Loogle and source searches also recorded. This did
not block the proof. No compilation tool failure or forced adaptation occurred.

## Second reading by T4

1. Compared the delivered modules with the repository versions. The original target
signatures and the three relocated data definitions are unchanged; the relocation is
declared in the change record. Verdict: passed.

2. Compiled all delivered modules with `lcompile.py --all` and searched for `sorry`,
axiom, unsafe, opaque, extern, implemented_by, and `debug.skipKernelTC`. No delivered
hole or forbidden declaration was found; imported `sorryAx` obligations are existing
dependencies. Verdict: passed.

3. Read each new theorem and node. The helper statements are strict reductions used by
the target proof, have source/docstring proofs, and no duplicate of an existing library
declaration was found. Verdict: passed.

4. Checked the proof route from the target downward and the import graph. The target
uses the canonical family, the one-model cocycle, and the transport lemma; removed
imports and pruned nodes are listed above, while the unit's realized route remains.
Verdict: passed.

5. Matched each node's `proof`, `proof_deps`, and `proof_origin` to the Lean proof and
confirmed the new node records contain the required metadata. Verdict: passed.

During review I restored the original target signature line wrapping, retained the
repository's existing node review metadata while updating its proof route, and moved this
section into the required report order. No proof or statement needed repair.

## New nodes

`def-pc-affine-coordinate-comparison-data`: the original three definitions, relocated
verbatim to break the data/theorem import cycle; no new choice of data.

`lem-pc-affine-coordinate-module-models`: concrete tilde/pushforward chart models,
their localization identification and K-flatness. Proved using existing tilde and
pullback K-flatness plus uniqueness of adjoints along a scheme isomorphism.

`lem-pc-perfect-hom-cochain-counit`: the exact counits and tensor composition mate used
by `perfectHomComposition`, their invertibility on K-flat models and their defining
composition equation. All are proved from existing derived universal properties.

`lem-pc-adjunction-square-composition`: generic pasting of invertible adjunction
squares. Proved by conjugation, whiskering formulas and inverse cancellation.

`lem-pc-counit-comparison-composition`: generic inverse-counit cocycle and naturality,
and transport by chart isomorphisms. Proved by naturality and cancellation.

`lem-pc-affine-coordinate-tensor-comparison`: explicit right-adjoint affine square,
its canonical mate and its composition equation, lifted to complexes and homotopy.
The global-sections coherence and all lifting glue are proved.

`lem-pc-affine-coordinate-derived-comparison`: inverse-counit object comparisons,
their chart conjugations and naturality for arbitrary maps between K-flat models;
assembly into the full two-label comparison family. No unproved construction remains.

`lem-pc-affine-coordinate-comparison-family-base`: the component formula for the
explicit canonical family. Proved by using the constructed family and reflexivity.

`lem-pc-affine-coordinate-comparison-chart-cocycle`: the one-model chart cocycle,
proved by combining the underived homotopy law, the fixed counit equation, and chart
conjugation. It does not assume a family composition law.

Change record: `coord/changes/T4-affine-coordinate-comparison-data.md`.
