## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.SelfTorAmbientLocalizedComparisons`
with a complete Lean reduction. A global K-flat resolution of the closed structure
sheaf computes the derived self-tensor by the existing natural K-flat comparison.
Applying derived homology and `homologyFunctorFactors` gives an actual sheaf
isomorphism from ordinary tensor homology to the required ambient homology.
Sectionwise evaluation transports the ordinary affine coordinates along this
isomorphism. Its naturality proves the final restriction equation.

The already-proved `exists_quotient_resolution_tensor_comparison` constructs psi,
a and k and all three algebraic identities from `ideal_le_comap_ideal`. There is
no localization/projectivity-of-localization step in this proof.

The remaining affine computation is stated in the new module
`Sheaf.AlgebraicGeometry.SelfTorOrdinaryResolutionSections`. It has no derived
category or derived tensor in its statement and constructs no algebraic lifts.
It compares explicit ordinary complexes, assuming an actual global augmented
K-flat resolution. Its docstring specifies the augmented tensor zigzag and
its naturality for supplied lifts. Existing statements, universes and public
imports of the item are unchanged. No definition or downstream module changes.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_selfTor_ambient_localized_comparisons`
(node `new-h2-self-tor-ambient-localized-comparisons`). The item now has no sorry.

Added: `AlgebraicGeometry.exists_selfTor_ordinary_resolution_sections`
(node `new-b3-self-tor-ordinary-resolution-sections`), the only new sorry.
This is a decomposition: one upper hole closed, one strictly lower ordinary
homology comparison added, net zero holes. It is not an unconditional completed
self-Tor proof. The derived-to-ordinary tensor transport, its homology transport,
the algebraic comparison construction and the final naturality transport are
fully proved in Lean.

Validation: both delivered modules compile through lcompile.py with no errors
or warnings. The new statement was checked at n=0, zero quotient (I=top), and
empty basic opens: the augmentation/tensor zigzag still computes degree zero,
and in the latter cases the relevant quotient/section modules are zero. No
nonzero-ring or nonempty-open assumption has been introduced.

## No longer needed

Removed direct proof imports from the item:
- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`, node
  `lem-pc-affine-derived-pullback-tensor-tilde`: no longer needed by this branch;
  the passage to derived tensor uses the K-flat comparison directly.
- `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`, node
  `lem-sc-affine-quotient-resolution-sheafification`: not needed by the completed
  upper proof, retained as a planned dependency of the ordinary affine computation.
- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`, node
  `lem-pc-bounded-above-flat-kflat`: likewise moved to the ordinary computation.

The upper node no longer needs `lem-weil-pbc-projective-resolution-lift` directly.
Its proposed localization-and-lifting route is replaced by the already-proved
`new-p4-quotient-resolution-tensor-comparison`, valid for arbitrary ring maps
preserving ideals. No claim is made that these nodes leave the whole target
closure: other branches may still use them. All unit-level statements and
steps remain; this node realizes no separate fixed unit step.

The source import graph of this module, excluding Mathlib, has 632 modules before this reduction and 403 afterward. 252 former dependencies are no longer on this branch; 23 dependencies are added. This is a branch calculation, not the global target-closure ledger.

Complete branch pruning list (module; DAG nodes where recorded):

- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullback`; `lem-pc-presheaf-module-inverse-image-adjunction`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackComparison`; `lem-pc-topological-module-pullback-comparison`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackRepresentatives`; `lem-pc-topological-pullback-common-representatives`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction`; `lem-pc-module-change-of-rings-adjunction`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkChangeOfRings`; `lem-weil-pbc-stalk-change-of-rings-tensor`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkChangeOfRingsPresheaf`; `lem-weil-pbc-presheaf-stalk-change-of-rings-tensor`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback`; `lem-pc-module-inverse-image-adjunction`
- `Sheaf.Algebra.Homology.AcyclicKFlatTensor`; `lem-pur-acyclic-kflat-tensor-arbitrary`
- `Sheaf.Algebra.Homology.BaseDerivedExtensionLinear`; `lem-pc-base-derived-extension-linear`
- `Sheaf.Algebra.Homology.BaseDerivedExtensionResolution`; `lem-pc-base-derived-extension-resolution`
- `Sheaf.Algebra.Homology.BaseDerivedExtensionScalar`; `lem-pc-base-derived-extension-scalar`
- `Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyAction`; `lem-pc-base-derived-tensor-cohomology-action`
- `Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel`; `def-pc-base-derived-tensor-cohomology-model`
- `Sheaf.Algebra.Homology.BaseDerivedTensorCounitLinear`; `lem-pc-base-derived-tensor-counit-linear`
- `Sheaf.Algebra.Homology.BaseTensorOrdinaryDegreeIso`; `lem-pc-base-tensor-ordinary-degree-iso`
- `Sheaf.Algebra.Homology.BaseTensorOrdinaryIso`; `lem-pc-base-tensor-ordinary-iso`
- `Sheaf.Algebra.Homology.ChangeOfRingsAcyclicKFlat`; `lem-pur-change-of-rings-acyclic-kflat`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso`; `lem-pur-change-of-rings-kflat-quasi-iso`
- `Sheaf.Algebra.Homology.ChangeOfRingsTensorAcyclic`; `lem-pur-change-of-rings-tensor-acyclic`
- `Sheaf.Algebra.Homology.ChangeOfRingsTensorComparison`; `lem-pur-change-of-rings-tensor-comparison`
- `Sheaf.Algebra.Homology.CoproductKProjective`; `lem-pc-coproduct-kprojective`
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`; `lem-pur-derived-change-of-rings`
- `Sheaf.Algebra.Homology.FilteredFreeKProjective`; `lem-pc-filtered-free-kprojective`, `lem-pc-filtered-free-kprojective-stage`, `lem-pc-filtered-free-kprojective-telescope`
- `Sheaf.Algebra.Homology.FilteredFreeKProjectiveAssembly`; `lem-pc-filtered-free-kprojective-assembly`
- `Sheaf.Algebra.Homology.FilteredFreeKProjectiveStep`; `lem-pc-filtered-free-kprojective-step`
- `Sheaf.Algebra.Homology.FilteredFreeResolution`; `lem-pc-derived-filtered-free-resolution`
- `Sheaf.Algebra.Homology.FilteredFreeTelescopeSplitting`; `lem-pc-filtered-free-telescope-splitting`
- `Sheaf.Algebra.Homology.FreeComplexCover`; `lem-pc-derived-free-complex-cover`
- `Sheaf.Algebra.Homology.FreeCoverBicomplex`; `lem-pc-derived-free-cover-bicomplex`
- `Sheaf.Algebra.Homology.FreeCoverColumns`; `lem-pc-derived-free-cover-columns`
- `Sheaf.Algebra.Homology.InverseImageStalkScalarTransport`; `lem-pc-ringed-inverse-image-stalk-scalar-transport`
- `Sheaf.Algebra.Homology.InverseImageStalkScalarTransportBeta`; `lem-pc-ringed-inverse-image-stalk-scalar-transport-beta`
- `Sheaf.Algebra.Homology.InverseImageStalkScalarTransportNaturality`; `lem-pc-ringed-inverse-image-stalk-scalar-transport-naturality`
- `Sheaf.Algebra.Homology.KFlatPullback`; `lem-pc-kflat-pullback-preservation`
- `Sheaf.Algebra.Homology.KFlatTensorProduct`; `lem-pc-kflat-tensor-product`
- `Sheaf.Algebra.Homology.KernelShiftedMappingCone`; `lem-weil-degreewise-epi-kernel-cocone-qis`
- `Sheaf.Algebra.Homology.LargeFilteredFreeResolution`; `lem-pc-large-filtered-free-resolution`
- `Sheaf.Algebra.Homology.LowerTruncationStepTriangle`; `lem-pc-derived-lower-truncation-step-triangle`
- `Sheaf.Algebra.Homology.QuasiIsoSaturatedTriangulated`; `lem-pur-quasi-isos-saturated-triangulated`
- `Sheaf.Algebra.Homology.RoosComparisonHomotopies`; `lem-weil-roos-comparison-homotopies`
- `Sheaf.Algebra.Homology.RoosComparisonHomotopyRetract`; `lem-weil-roos-comparison-homotopy-retract`
- `Sheaf.Algebra.Homology.RoosComparisonMaps`; `lem-weil-roos-comparison-maps`
- `Sheaf.Algebra.Homology.RoosComplex`; `lem-weil-derived-limit-roos-complex`
- `Sheaf.Algebra.Homology.RoosSplitComparison`; `lem-weil-roos-split-comparison`
- `Sheaf.Algebra.Homology.TensorActionOfAdditiveFunctor`; `lem-pc-tensor-action-additive-functor`
- `Sheaf.Algebra.Homology.TensorPullbackStalkComplex`; `lem-pc-tensor-pullback-stalk-complex`
- `Sheaf.Algebra.Homology.TotalFreeFiltration`; `lem-pc-derived-total-free-filtration`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationCokernelEven`; `lem-pc-derived-total-filtration-cokernel-even`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationCokernelOdd`; `lem-pc-derived-total-filtration-cokernel-odd`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationCokernelOddAux`; `lem-pc-derived-total-filtration-cokernel-odd-core`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationEvenQuotientBijective`; `lem-pc-derived-total-filtration-even-quotient-bijective`, `lem-pc-derived-total-filtration-even-quotient-injective`, `lem-pc-derived-total-filtration-even-quotient-surjective`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationEvenQuotientMap`; `lem-pc-derived-total-filtration-even-quotient-map`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationExhaustive`; `lem-pc-derived-total-filtration-exhaustive`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationOddQuotientBijective`; `lem-pc-derived-total-filtration-odd-quotient-bijective`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationOddQuotientMap`; `lem-pc-derived-total-filtration-odd-quotient-map`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationQuotients`; `lem-pc-derived-total-filtration-quotients`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationStepRetraction`; `lem-pc-derived-total-filtration-step-retraction`
- `Sheaf.Algebra.Homology.TotalFreeFiltrationTerms`; `lem-pc-derived-total-filtration-stable`
- `Sheaf.Algebra.Homology.TowerEvaluationKInjective`; `lem-weil-tower-evaluation-kinjective`
- `Sheaf.Algebra.Homology.TowerSplitComplexReplacement`; `lem-weil-tower-split-complex-replacement`
- `Sheaf.Algebra.Homology.ZeroDifferentialFreeCoproduct`; `lem-pc-zero-differential-free-coproduct`
- `Sheaf.AlgebraicGeometry.AffineDerivedCounitHomologyFactorization`; `new-affine-derived-counit-homology-factorization`
- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`; `lem-pc-affine-derived-pullback-tensor-tilde`
- `Sheaf.AlgebraicGeometry.AffineDerivedSectionsHomologyComparison`; `lem-pc-affine-derived-sections-homology-comparison`
- `Sheaf.AlgebraicGeometry.AffineDerivedSectionsTruncatedBottom`; `new-affine-derived-sections-truncated-bottom`
- `Sheaf.AlgebraicGeometry.AffineDerivedSectionsTruncationIso`; `new-affine-derived-sections-truncation-iso`
- `Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison`; `new-affine-derived-tilde-homology-comparison`
- `Sheaf.AlgebraicGeometry.AffineDerivedUnitHomologyIsIso`; `new-affine-derived-unit-homology-isIso`
- `Sheaf.AlgebraicGeometry.AffineDerivedUnitIsomorphism`; `lem-pc-affine-derived-unit-isomorphism`
- `Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing`; `pqf-lem-affine-vanishing`
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedAdjunctionConstruction`; `new-affine-qcoh-derived-adjunction-construction`
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedAdjunctionUnitCounit`; `new-affine-qcoh-derived-adjunction-unit-counit`
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`; `lem-pc-affine-qcoh-derived-equivalence`
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore`; `new-affine-qcoh-derived-equivalence-core`
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceShift`; `new-affine-qcoh-derived-equivalence-shift`
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedTildeTriangulated`; `new-affine-qcoh-derived-tilde-triangulated`
- `Sheaf.AlgebraicGeometry.AffineTildeDerivedSectionsUnitIsIso`; `new-affine-tilde-derived-sections-unit-isIso`
- `Sheaf.AlgebraicGeometry.AffineTildeTotalTensor`; `lem-pc-affine-tilde-total-tensor`
- `Sheaf.AlgebraicGeometry.Coherent`; `pqf-def-coherent`
- `Sheaf.AlgebraicGeometry.DerivedFunctorTruncationStabilization`; `lem-pc-derived-functor-truncation-stabilization`
- `Sheaf.AlgebraicGeometry.DerivedPullback`; `def-pc-derived-pullback`
- `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel`; `lem-pc-derived-pullback-kflat-tensor-model`
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent`; `lem-pc-derived-pullback-tensor-comparison-descent`
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct`; `lem-pc-derived-pullback-tensor-product`
- `Sheaf.AlgebraicGeometry.InverseImageExactKFlat`; `lem-pc-inverse-image-exact-kflat-resolution`
- `Sheaf.AlgebraicGeometry.InverseImageModuleFunctor`; `lem-pc-inverse-image-module-functor-exact`
- `Sheaf.AlgebraicGeometry.InverseImageTensorPullbackComparison`; `lem-pc-inverse-image-tensor-pullback-comparison`
- `Sheaf.AlgebraicGeometry.KFlatBifunctorIsoDescent`; `lem-pc-kflat-bifunctor-iso-descent`
- `Sheaf.AlgebraicGeometry.MLSetsTowerLimitNonempty`; `lem-weil-pbc-ml-sets-tower-limit-nonempty`
- `Sheaf.AlgebraicGeometry.ModuleAbelianZariskiCohomology`; no module record found in the DAG
- `Sheaf.AlgebraicGeometry.ModulePullbackTensor`; `lem-weil-pbc-module-pullback-tensor`
- `Sheaf.AlgebraicGeometry.Modules.InverseImageStalkScalarTransport`; `lem-pc-inverse-image-stalk-scalar-transport`
- `Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde`; `lem-pc-affine-tilde-kflat`
- `Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk`; `lem-weil-pbc-module-stalk-pullback`
- `Sheaf.AlgebraicGeometry.Modules.TensorPullbackTensorIsIso`; `lem-weil-pbc-module-pullback-tensor-iso-criterion`
- `Sheaf.AlgebraicGeometry.Modules.TildeStalkTensorComparison`; `lem-pc-affine-tilde-stalk-tensor-comparison`
- `Sheaf.AlgebraicGeometry.OpenModuleCohomologyComparison`; `lem-pqf-open-module-cohomology-comparison`
- `Sheaf.AlgebraicGeometry.QCohTruncationDerivedLimit`; `lem-pc-qcoh-truncation-derived-limit`
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`; `def-pc-ringed-spaces-derived-direct-image`
- `Sheaf.AlgebraicGeometry.RingedSpaceSheafificationCohomology`; `lem-pc-ringed-space-sheafification-cohomology`
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`; `def-pc-derived-direct-image`
- `Sheaf.AlgebraicGeometry.TensorPullback`; `def-pc-module-pullback`, `lem-pc-module-pullback-identity-composition`
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`; `lem-pc-module-pullback-adjunction`
- `Sheaf.AlgebraicGeometry.TensorPullbackKFlatQuasiIso`; `lem-pc-tensor-pullback-kflat-quasi-iso`
- `Sheaf.AlgebraicGeometry.TensorPullbackTilde`; `lem-weil-pbc-tilde-pullback-base-change`
- `Sheaf.AlgebraicGeometry.TruncationDerivedLimit`; `lem-pc-ringed-space-truncation-derived-limit`
- `Sheaf.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound`; `lem-pc-unbounded-derived-functor-cohomological-bound`
- `Sheaf.AlgebraicTopology.SetCechNerveFreeResolution`; `lem-weil-pbc-set-cech-nerve-free-resolution`
- `Sheaf.CategoryTheory.Abelian.ExtEpiEffacement`; `lem-sc-ext-epi-effacement`
- `Sheaf.CategoryTheory.Abelian.HorseshoeDefectFactorization`; `lem-weil-pbc-horseshoe-defect-factorization`
- `Sheaf.CategoryTheory.Abelian.HorseshoeDegreewiseMap`; `lem-weil-pbc-horseshoe-degreewise-map`
- `Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor`; `lem-weil-pbc-horseshoe-delta-functor`
- `Sheaf.CategoryTheory.Abelian.HorseshoeHomotopyCorrection`; `lem-weil-pbc-horseshoe-homotopy-correction`
- `Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLift`; `lem-weil-pbc-horseshoe-correction`, `lem-weil-pbc-horseshoe-morphism-lift`, `lem-weil-pbc-horseshoe-preliminary-data`
- `Sheaf.CategoryTheory.Abelian.HorseshoePrescribedResolutions`; `lem-sp-horseshoe-prescribed-resolutions`
- `Sheaf.CategoryTheory.Abelian.HorseshoePrescribedRows`; `lem-sp-horseshoe-prescribed-row-construction`
- `Sheaf.CategoryTheory.Abelian.HorseshoeResolutions`; `lem-weil-pbc-injective-resolution-ses`
- `Sheaf.CategoryTheory.DeltaFunctor`; `def-weil-pbc-delta-functor`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantCofinal`; `lem-pur-essential-constant-cofinal-0a1s`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro`; `def-pc-essentially-constant-pro-diagram`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProCriterion`; `lem-pur-essential-constant-pro-criterion-05py`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProHomColimit`; `lem-pc-essentially-constant-pro-hom-colimit`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedExactOfLocalization`; `lem-pur-left-derived-exact-chosen-localization`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`; `lem-pur-left-derived-from-kflat-class`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge`; `lem-pur-left-derived-defined-pointwise-kan-bridge`
- `Sheaf.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy`; `lem-pur-resolving-class-essential-constancy`
- `Sheaf.CategoryTheory.DerivedFunctorShift`; `lem-pur-derived-functor-shift-05su`
- `Sheaf.CategoryTheory.DerivedFunctorThirdValue`; `lem-pur-derived-functor-triangles-05sc-third-value`
- `Sheaf.CategoryTheory.DerivedFunctorTriangleRetractionHomColimit`; `lem-pur-triangle-retraction-hom-colimit`
- `Sheaf.CategoryTheory.DerivedFunctorTriangles`; `lem-pur-derived-functor-triangles-05sc`
- `Sheaf.CategoryTheory.DerivedFunctorValueTriangle`; `lem-pur-derived-functor-triangles-05sc-value-triangle`
- `Sheaf.CategoryTheory.DerivedFunctorValueTriangleCompatibility`; `lem-pur-derived-functor-triangles-05sc-value-triangle-compatibility`
- `Sheaf.CategoryTheory.DerivedLimitEventuallyIso`; `lem-pc-derived-limit-eventually-iso`
- `Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups`; `lem-pc-derived-limit-roos-abelian-groups`, `lem-pc-tower-enough-injectives`
- `Sheaf.CategoryTheory.EffaceableDeltaFunctorSuccessor`; `lem-weil-pbc-effaceable-delta-functor-successor`
- `Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal`; `lem-weil-pbc-effaceable-delta-functor-universal`
- `Sheaf.CategoryTheory.EffacingSequenceComparison`; `lem-weil-pbc-effacing-sequence-comparison`
- `Sheaf.CategoryTheory.EffacingSequencePushout`; `lem-weil-pbc-effacing-sequence-pushout`
- `Sheaf.CategoryTheory.InjectiveModulePresheaf`; `lem-weil-pbc-ringed-site-injective-module-injective-presheaf`
- `Sheaf.CategoryTheory.InjectiveSplitTower`; `lem-pc-injective-split-tower-injective`
- `Sheaf.CategoryTheory.InjectiveSplitTowerExtension`; `lem-pc-injective-split-tower-extension`
- `Sheaf.CategoryTheory.InjectiveTowerEmbedding`; `lem-pc-tower-injective-embedding`
- `Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`; `def-pur-saturated-triangulated-localization`
- `Sheaf.CategoryTheory.LeftDerivedExactWhenDefined`; `lem-pur-left-derived-exact-when-defined`
- `Sheaf.CategoryTheory.LeftDerivedKanSourceTriangles`; `lem-pur-left-derived-kan-source-triangles`
- `Sheaf.CategoryTheory.LeftDerivedKanTriangleValueComparison`; `lem-pur-left-derived-kan-triangle-value-comparison`
- `Sheaf.CategoryTheory.LeftDerivedValueMorphism`; `lem-pur-derived-functor-morphisms-05sa`
- `Sheaf.CategoryTheory.Limits.TowerTransitionEndomorphism`; `def-weil-tower-transition-endomorphism`
- `Sheaf.CategoryTheory.MittagLefflerLimitExact`; `lem-weil-pbc-mittag-leffler-limit-exact`
- `Sheaf.CategoryTheory.PresheafChangeOfRingsAdjunction`; `lem-pc-presheaf-change-of-rings-adjunction`
- `Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso`; `lem-weil-pbc-derived-functor-truncation-iso`, `lem-weil-pbc-derived-functor-truncation-iso-epi`, `lem-weil-pbc-derived-functor-truncation-iso-mono`
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`; `lem-weil-pbc-right-derived-universal-delta-functor`
- `Sheaf.CategoryTheory.RightKanExtensionCoherentShift`; `lem-pur-right-kan-extension-coherent-shift`
- `Sheaf.CategoryTheory.RoosAcyclicResolution`; `lem-pc-roos-functorial-acyclic-resolution`
- `Sheaf.CategoryTheory.RoosFinitePrefixLimits`; `lem-pc-roos-finite-prefix-limits`
- `Sheaf.CategoryTheory.RoosFinitePrefixes`; `lem-pc-roos-finite-prefix-construction`
- `Sheaf.CategoryTheory.RoosPrefixAcyclic`; `lem-pc-roos-prefix-acyclic`
- `Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation`; `new-sheaf-cohomology-derived-evaluation`
- `Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic`; `lem-sc-injective-module-abelian-acyclic-zariski`
- `Sheaf.CategoryTheory.Sites.InjectivePresheafModuleNerveAcyclic`; `lem-sc-injective-presheaf-module-nerve-acyclic`
- `Sheaf.CategoryTheory.Sites.PresheafCechComplex`; `def-sc-presheaf-cech-complex`
- `Sheaf.CategoryTheory.Sites.PresheafCechExtEdgeInjective`; `lem-sc-presheaf-cech-ext-edge-injective`
- `Sheaf.CategoryTheory.Sites.PresheafCechExtEdgeKernel`; `lem-sc-presheaf-cech-ext-edge-kernel`
- `Sheaf.CategoryTheory.Sites.PresheafCechSheafAugmentationExact`; `lem-sc-presheaf-cech-sheaf-augmentation-exact`
- `Sheaf.CategoryTheory.Sites.PresheafCechSheafHomComparison`; `lem-sc-presheaf-cech-sheaf-hom-comparison`
- `Sheaf.CategoryTheory.Sites.PresheafCechSheafPositiveExact`; `lem-sc-presheaf-cech-sheaf-positive-exact`
- `Sheaf.CategoryTheory.Sites.PresheafCechSheafResolution`; `lem-sc-presheaf-cech-sheaf-resolution`
- `Sheaf.CategoryTheory.Sites.PresheafCechVanishingCriterion`; `lem-sc-presheaf-cech-vanishing-criterion`
- `Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling`; `lem-sc-presheaf-free-ext-local-killing`, `lem-sc-presheaf-free-ext-local-killing-witness`
- `Sheaf.CategoryTheory.Sites.PresheafFreeNerveComparison`; `lem-sc-presheaf-free-nerve-comparison`
- `Sheaf.CategoryTheory.Sites.PresheafFreeNerveExact`; `lem-sc-presheaf-free-nerve-exact`, `lem-sc-presheaf-free-nerve-exact-eval`, `lem-sc-presheaf-free-nerve-exact-eval-glue`
- `Sheaf.CategoryTheory.ThirdValueConstruction`; `lem-pur-derived-functor-triangles-05sc-third-value-core`
- `Sheaf.CategoryTheory.TowerSplitEnvelope`; `lem-weil-tower-split-envelope`
- `Sheaf.CategoryTheory.TriangleCommonRefinement`; `lem-pur-triangle-common-refinement-ms3-05r9`
- `Sheaf.CategoryTheory.TriangleMorphismCategory`; `lem-pur-triangle-morphism-category-05r9`
- `Sheaf.CategoryTheory.Triangulated.DenominatorTriangleCompletion`; `lem-pur-triangle-completion-ms6-05r9`
- `Sheaf.CategoryTheory.Triangulated.DerivedCountableProductsCore`; `lem-weil-derived-countable-products-core`
- `Sheaf.CategoryTheory.Triangulated.DerivedCountableProductsExistence`; `lem-weil-derived-countable-products-existence`
- `Sheaf.CategoryTheory.Triangulated.DerivedCountableProductsProperties`; `lem-weil-derived-countable-products-properties`
- `Sheaf.CategoryTheory.Triangulated.DerivedFunctorDerivedLimit`; `lem-pc-derived-functor-commutes-derived-limit`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimit`; `def-weil-derived-limit`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence`; `lem-weil-derived-limit-existence`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts`; `lem-weil-derived-limit-products-core`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitTower`; `lem-weil-derived-limit-tower-core`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerCone`; `lem-weil-derived-limit-tower-core-cone`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerProperty`; `lem-weil-derived-limit-tower-core-property`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerRoosTriangle`; `lem-weil-derived-limit-tower-roos-triangle`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerTriangle`; `lem-weil-derived-limit-tower-core-property-triangle`
- `Sheaf.CategoryTheory.Triangulated.MilnorBoundaryFactorization`; `lem-pc-milnor-boundary-factorization`
- `Sheaf.CategoryTheory.Triangulated.MilnorProjectionFactorization`; `lem-pc-milnor-projection-factorization`
- `Sheaf.CategoryTheory.Triangulated.MilnorSequence`; `lem-pc-derived-limit-milnor-sequence`
- `Sheaf.CategoryTheory.Triangulated.RightDerivedFunctorCountableProducts`; `lem-pc-right-derived-functor-countable-products`
- `Sheaf.CategoryTheory.Triangulated.RingedSpaceDerivedProducts`; `lem-pc-ringed-space-derived-products`
- `Sheaf.CategoryTheory.TriangulatedHomColimitComparison`; `lem-pur-triangulated-hom-colimit-comparison`
- `Sheaf.Paper.DerivedTotalResolutionColumnZero`; `lem-pc-derived-total-resolution-column-zero`
- `Sheaf.Paper.DerivedTotalResolutionHomologyInjective`; `lem-pc-derived-total-resolution-homology-injective`
- `Sheaf.Paper.DerivedTotalResolutionHomologySurjective`; `lem-pc-derived-total-resolution-homology-surjective`
- `Sheaf.Paper.DerivedTotalResolutionQuasiIso`; `lem-pc-derived-total-resolution-quasi-iso`
- `Sheaf.Paper.PQFCohomology`; `pqf-def-cohomology`
- `Sheaf.Paper.TotalResolutionCycleFiniteSupport`; `aux-total-resolution-cycle-finite-support`
- `Sheaf.Paper.TotalResolutionCycleReduction`; `lem-pc-derived-total-resolution-column-zero-cycle-reduction`
- `Sheaf.Paper.TotalResolutionCycleSupportStep`; `aux-total-resolution-cycle-support-step`
- `Sheaf.Paper.TotalResolutionCycleSupportZero`; `aux-total-resolution-cycle-support-zero`
- `Sheaf.Topology.CohomologyPresheafDerivedSectionsEvaluation`; `lem-pc-cohomology-presheaf-derived-sections-evaluation`
- `Sheaf.Topology.DerivedLimitStalkInjective`; `lem-pc-ringed-space-derived-limit-stalk-injective`
- `Sheaf.Topology.InverseImageModule`; `def-pc-topological-inverse-image-module`
- `Sheaf.Topology.InverseImageOperationExt`; `lem-pc-inverse-image-operation-ext`
- `Sheaf.Topology.InverseImagePresheafModule`; `lem-pc-inverse-image-presheaf-module`
- `Sheaf.Topology.InverseImageStalk`; `lem-weil-pbc-topological-inverse-image-stalk`
- `Sheaf.Topology.OpenModuleCohomology`; `def-sc-open-module-cohomology`
- `Sheaf.Topology.OpenModuleDerivedSections`; `def-pc-open-module-derived-sections`
- `Sheaf.Topology.PointwiseTruncationLimit`; `lem-pc-ringed-space-pointwise-truncation-limit`
- `Sheaf.Topology.PointwiseTruncationLimitExists`; `lem-pc-ringed-space-pointwise-truncation-limit-exists`
- `Sheaf.Topology.PointwiseTruncationLimitIsIso`; `lem-pc-ringed-space-pointwise-truncation-limit-isIso`
- `Sheaf.Topology.PointwiseTruncationOpenStabilization`; `lem-pc-pointwise-truncation-open-stabilization`
- `Sheaf.Topology.RestrictInjectiveResolution`; `lem-sc-ringed-space-restrict-injective-resolution`
- `Sheaf.Topology.RingedSpaceModuleCohomology`; `def-sc-ringed-space-module-cohomology`, `def-sc-sheaf-cohomology-functor`
- `Sheaf.Topology.RingedSpaceModuleEnoughInjectives`; `lem-sc-ringed-space-module-sheaves-enough-injectives`
- `Sheaf.Topology.RingedSpaceRGammaDerivedLimit`; `lem-pc-ringed-space-rgamma-derived-limit`
- `WeilConjectures.Algebra.Homology.HomotopyCategory.Products`; no module record found in the DAG
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`; `lem-pc-affine-cech-complex`, `lem-pc-affine-vanishing`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`; `def-pc-euler-characteristic`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`; `def-sp-acyclic`, `lem-weil-pbc-leray-acyclicity-quasi-iso`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`; `lemma-weil-pbc-leray-acyclicity`
- `WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage`; no module record found in the DAG
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`; no module record found in the DAG
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`; `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`; no module record found in the DAG
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`; no module record found in the DAG
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`; `prop-weil-pbc-derived-inverse-image-adjunction`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic`; no module record found in the DAG
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`; no module record found in the DAG
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`; `src-right-derived-functor-plus-compatibility`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology`; `src-right-derived-functor-plus-acyclic-unit`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`; `lem-sp-derived-functor-single-identification`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`; `lem-pc-right-derived-functor-triangulated`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`; no module record found in the DAG
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`; no module record found in the DAG
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty`; no module record found in the DAG
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`; `lem-weil-pbc-derived-direct-image-triangulated`, `lem-weil-pbc-derived-functor-negative-vanishing`
- `WeilConjectures.Mathlib.Algebra.Homology.Embedding.Extend`; no module record found in the DAG
- `WeilConjectures.Mathlib.Algebra.Homology.HomologySequence`; no module record found in the DAG
- `WeilConjectures.Mathlib.AlgebraicGeometry.Scheme`; `lem-pc-scheme-connected-iff-idempotents`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution`; no module record found in the DAG
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived`; no module record found in the DAG
- `WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Orthogonal`; no module record found in the DAG
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`; `lem-sp-right-adjoint-preserves-injectives`
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Resolution`; no module record found in the DAG
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor`; `lem-weil-pbc-commshift-nattrans-triangle-morphism`
- `WeilConjectures.Mathlib.RingTheory.LocalRing.Basic`; `lem-weil-pbc-local-ring-idempotent-zero-one`
- `WeilConjectures.Topology.Sheaves.Cech`; `lem-pc-topological-injective-cech-positive-exact`
- `WeilConjectures.Topology.Sheaves.CechCriterion`; `lem-pc-topological-ses-cech-sections-surjective`

## Where the brief, the DAG or earlier work was wrong

The old plan unnecessarily localized the source projective resolution before
constructing an algebraic lift. Exact restriction of scalars plus projectivity
of the source suffices, and the existing quotient-resolution comparison already
implements it. The old general affine derived tensor API does not itself state
the required quotient-resolution section coordinates or their scalar-transport
normalization. The ordinary affine comparison remains a substantive geometric
step, now isolated without repeating the target's derived tensor or lift
existence. No disputed statement or interface correction was found.

The generalized ordinary statement is true for every supplied augmented lift:
the explicit tensor zigzags commute before homology. It does not assume
compatibility for arbitrary unnormalized choices of affine isomorphisms.

## New nodes

`new-b3-self-tor-ordinary-resolution-sections`: the ordinary homology comparison
for a given global K-flat resolution, with compatibility for supplied algebraic
lifts. Source: [Stacks 08DX(2)](https://stacks.math.columbia.edu/tag/08DX),
[06YG](https://stacks.math.columbia.edu/tag/06YG),
[06YB](https://stacks.math.columbia.edu/tag/06YB) and
[01I9](https://stacks.math.columbia.edu/tag/01I9).
LeanFinder/Loogle returned supporting Tor and tilde APIs; LeanSearch was
unavailable and is recorded without a mathematical verdict. Local source
searches found the algebraic lifts, ordinary chart tensor comparison and
open K-flat homology comparison, but no matching simultaneous affine section
comparison. Blueprint search found no duplicate. No change record is needed.

## Second reading by B3

1. Compared the delivered ambient module with the repository version. Existing theorem
   signatures are unchanged; only proof and proof-only imports changed. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; there are no errors or
   warnings, and the only remaining `sorry` is the named ordinary-resolution theorem.
   Verdict: pass.
3. Reviewed the split-off statement and node. It is a strictly lower ordinary homology
   comparison, with a complete source and proof sketch, and its edge cases are recorded.
   No duplicate library declaration was found. Verdict: pass.
4. Checked the proof route and pruning. The upper proof uses the quotient-resolution
   comparison and K-flat derived tensor comparison; the unit-level route is retained.
   Removed imports and former dependencies are listed above. Verdict: pass.
5. Checked the DAG records against the Lean declarations and imports, including the new
   node's `lean` record and the item's updated proof dependencies. Verdict: pass.

Changed in this second reading: added this review record only; no Lean statements or
proofs required repair.
