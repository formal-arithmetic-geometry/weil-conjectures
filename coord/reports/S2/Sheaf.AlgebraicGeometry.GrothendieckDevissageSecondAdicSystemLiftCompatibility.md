## What changed

Completed both holes in
`lean/Sheaf/AlgebraicGeometry/GrothendieckDevissageSecondAdicSystemLiftCompatibility.lean`.
Every existing declaration signature and visibility is unchanged. No definition changed,
no module was adapted, and no new theorem or DAG node was introduced.

`torsion_completion_bijective` raises the two annihilating exponents to their maximum,
proves support on the common closed thickening from the public affine ideal-power and
tensor-section formulas, and applies the existing supported-completion Hom bijection.
The public theorem constructs the double natural transformation from sigma, reduced
alpha, and theta inverse; lifts every component using this bijection; proves adjacent
compatibility using injectivity and naturality; and assembles delta with
`NatTrans.ofOpSequence`. Evaluating the lifting equation and cancelling theta inverse
proves the required comparison squares.

Replaced the imports of `GrothendieckExistenceSupportedHom` and
`IdealPowerProductRestrictionZero` with the precise public APIs used by the proof.
Endpoint transport through isomorphisms now uses `Iso.homCongr` directly. All retained
proof imports were checked by removing each in turn and compiling; each is needed.
The trial import `WeilConjectures.AlgebraicGeometry.Modules.TensorSection` was removed
because it was redundant. The original public imports are unchanged.

Updated only `proof`, `proof_deps`, and `proof_origin` of the existing node
`lem-weil-pbc-devissage-second-adic-system-lift-compatibility` to describe the actual
proof. Its statement, statement dependencies, and Lean signature are unchanged.
The unit's route and realized nodes are unchanged.

Validation: the module compiles cleanly with lcompile.py. An independent scratch copy
with `#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound` for
`AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_lift_compatibility`.
There are zero textual or direct proof holes in the delivered module and no lines over
100 characters. Import-direction checks permit the added dependencies.

Search: Lean Finder for lifting natural transformations returned
`Functor.FullyFaithful.preimage`; Loogle confirmed the fully-faithful API; Mathlib grep
confirmed `NatTrans.ofOpSequence`. Local searches found no existing implementation of
the target theorem. The construction follows Stacks `coherent.tex`, Tag 088A,
`lemma-existence-tricky`, lines 6961--6989. Zero module/ideal and empty-affine cases use
the same image, tensor, and sheaf-separatedness arguments without any extra hypotheses.

## Proved and sorry left

Holes closed (2):

- `AlgebraicGeometry.torsion_completion_bijective` (existing private helper).
- `AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_lift_compatibility`
  (`lem-weil-pbc-devissage-second-adic-system-lift-compatibility`).

Holes added: 0. Split-offs: 0. Holes left in the item: 0. This is a proof, not a
decomposition. The pre-existing `supported_completion_bijective` and
`annihilated_higher_power` remain proved.

## No longer needed

Removed direct imports:

- `Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedHom`.
- `Sheaf.AlgebraicGeometry.IdealPowerProductRestrictionZero`.

The private endpoint helper from the first module and the private `power_mono`,
`power_subobject`, and `product_iso` helpers from the second module are not used.
The DAG no longer needs `lem-weil-pbc-ideal-power-product-restriction-zero` for this
proof. It instead cites the public affine ideal-times and tensor-section nodes and
the coherence criterion.

The following complete list is the difference between this module's old and new
source import closures (196 modules). It is local to this item: another target branch
may still import one of these modules. No claim of global target pruning is made.

- `Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge`.
- `Sheaf.AlgebraicGeometry.AffinePushforwardIdealProduct`.
- `Sheaf.AlgebraicGeometry.ClosedImmersionIdealPowerAnnihilation`.
- `Sheaf.AlgebraicGeometry.ClosedImmersionPowerQuotient`.
- `Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`.
- `Sheaf.AlgebraicGeometry.CoherentSheafHom`.
- `Sheaf.AlgebraicGeometry.CoherentThickeningSystem`.
- `Sheaf.AlgebraicGeometry.CohomologyPowersIdealApplication`.
- `Sheaf.AlgebraicGeometry.CohomologyPowersIdealImageBound`.
- `Sheaf.AlgebraicGeometry.CohomologyPowersIdealKernelBound`.
- `Sheaf.AlgebraicGeometry.CohomologyPowersIdealReesFinite`.
- `Sheaf.AlgebraicGeometry.CohomologyPowersIdealTransitionMaps`.
- `Sheaf.AlgebraicGeometry.CompletionFromRestriction`.
- `Sheaf.AlgebraicGeometry.CompletionInternalHom`.
- `Sheaf.AlgebraicGeometry.FormalCompletionFullyFaithfulProper`.
- `Sheaf.AlgebraicGeometry.FormalCompletionMapInjectiveProper`.
- `Sheaf.AlgebraicGeometry.FormalCompletionMapSurjectiveProper`.
- `Sheaf.AlgebraicGeometry.FormalFunctionsCompleteBase`.
- `Sheaf.AlgebraicGeometry.FormalFunctionsPowerKernel`.
- `Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedHom`.
- `Sheaf.AlgebraicGeometry.IdealModuleProductStalk`.
- `Sheaf.AlgebraicGeometry.IdealPowerProductRestrictionZero`.
- `Sheaf.AlgebraicGeometry.IdealPowerProductZeroAffineCover`.
- `Sheaf.AlgebraicGeometry.IdealPowersReesGradedData`.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyScalarEndomorphism`.
- `Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison`.
- `Sheaf.AlgebraicGeometry.ModulePullbackFiniteType`.
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`.
- `Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum`.
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`.
- `Sheaf.AlgebraicGeometry.TheoremFormalFunctions`.
- `Sheaf.AlgebraicGeometry.ThickeningCompletionHomDictionary`.
- `Sheaf.AlgebraicGeometry.ThickeningSystemComparisonTransport`.
- `Sheaf.AlgebraicGeometry.ThickeningSystemHomTransport`.
- `Sheaf.AlgebraicGeometry.ThickeningSystemHomTransportCore`.
- `Sheaf.AlgebraicGeometry.ThickeningSystemPushforward`.
- `Sheaf.AlgebraicGeometry.ThickeningSystemPushforwardAdic`.
- `Sheaf.AlgebraicGeometry.ThickeningSystemPushforwardAssembly`.
- `Sheaf.AlgebraicGeometry.ThickeningSystemPushforwardLifting`.
- `Sheaf.AlgebraicGeometry.ThickeningSystemPushforwardTermwiseLift`.
- `Sheaf.AlgebraicGeometry.ThickeningSystemsCompletionComparison`.
- `Sheaf.AlgebraicGeometry.ThickeningSystemsDictionary`.
- `Sheaf.AlgebraicGeometry.ThickeningSystemsEquivalence`.
- `Sheaf.Paper.GradedCohomologyModuleFinite`.
- `Sheaf.Paper.GradedCohomologyModuleStructure`.
- `Sheaf.Paper.GradedFinitenessCohomology`.
- `Sheaf.Paper.GradedModuleRelativeSpecRealization`.
- `Sheaf.Paper.MLCohomologyPowersIdeal`.
- `Sheaf.Paper.MLCohomologyPowersIdealImageStabilization`.
- `Sheaf.Paper.MLCohomologyPowersIdealKernelBound`.
- `Sheaf.RingTheory.FiniteModuleComplete`.
- `WeilConjectures.Algebra.FiniteReesModuleGeneration`.
- `WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`.
- `WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting`.
- `WeilConjectures.Algebra.Module.AdicCompletionStableRanges`.
- `WeilConjectures.Algebra.Module.ReesKernelGenerators`.
- `WeilConjectures.AlgebraicGeometry.AffineAlgebraLocalMaps`.
- `WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleGenerators`.
- `WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleKernel`.
- `WeilConjectures.AlgebraicGeometry.AffineAlgebraModulePresentation`.
- `WeilConjectures.AlgebraicGeometry.AffineBaseChangeSectionsInduction`.
- `WeilConjectures.AlgebraicGeometry.AffineBasisRingActionGluing`.
- `WeilConjectures.AlgebraicGeometry.AffineInternalHomEvaluationBijective`.
- `WeilConjectures.AlgebraicGeometry.AffineModuleCorrespondence`.
- `WeilConjectures.AlgebraicGeometry.AffineModuleFiniteType`.
- `WeilConjectures.AlgebraicGeometry.AffineModuleTensorAlgebraQuasiCoherent`.
- `WeilConjectures.AlgebraicGeometry.AffineModuleTensorBaseChange`.
- `WeilConjectures.AlgebraicGeometry.AffineModuleTensorCoherenceComparisons`.
- `WeilConjectures.AlgebraicGeometry.AffineModuleTensorComparisonIsIso`.
- `WeilConjectures.AlgebraicGeometry.AffineModuleTensorConstruction`.
- `WeilConjectures.AlgebraicGeometry.AffineModuleTensorCounitFactor`.
- `WeilConjectures.AlgebraicGeometry.AffineModuleTensorCounitLinear`.
- `WeilConjectures.AlgebraicGeometry.AffineModuleTensorCounitSmul`.
- `WeilConjectures.AlgebraicGeometry.AffineModuleTensorExtensionUnit`.
- `WeilConjectures.AlgebraicGeometry.AffineModuleTensorUnitLift`.
- `WeilConjectures.AlgebraicGeometry.AffineModuleTensorUnitSections`.
- `WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge`.
- `WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`.
- `WeilConjectures.AlgebraicGeometry.AffinePushforwardFreeEvaluation`.
- `WeilConjectures.AlgebraicGeometry.AffinePushoutFirstTensorSections`.
- `WeilConjectures.AlgebraicGeometry.AffinePushoutModuleSectionPresentation`.
- `WeilConjectures.AlgebraicGeometry.AffinePushoutRingAffineSections`.
- `WeilConjectures.AlgebraicGeometry.AffinePushoutRingSectionComm`.
- `WeilConjectures.AlgebraicGeometry.AffinePushoutRingSectionDelta`.
- `WeilConjectures.AlgebraicGeometry.AffinePushoutRingSectionMap`.
- `WeilConjectures.AlgebraicGeometry.AffinePushoutRingSectionMapInjective`.
- `WeilConjectures.AlgebraicGeometry.AffinePushoutRingSectionMapTmul`.
- `WeilConjectures.AlgebraicGeometry.AffinePushoutRingSectionProducts`.
- `WeilConjectures.AlgebraicGeometry.AffineStructureAlgebraFullyFaithful`.
- `WeilConjectures.AlgebraicGeometry.AffineTensorUnitSectionPresentation`.
- `WeilConjectures.AlgebraicGeometry.BalancedActionAffineOpen`.
- `WeilConjectures.AlgebraicGeometry.BalancedActionAffineSections`.
- `WeilConjectures.AlgebraicGeometry.BalancedActionDirectImageModule`.
- `WeilConjectures.AlgebraicGeometry.BalancedActionQuasicoherentRealization`.
- `WeilConjectures.AlgebraicGeometry.BasicPropertiesDegreeZero`.
- `WeilConjectures.AlgebraicGeometry.BasicPropertiesIdentity`.
- `WeilConjectures.AlgebraicGeometry.BasicPropertiesLinearity`.
- `WeilConjectures.AlgebraicGeometry.BasicPropertiesRestriction`.
- `WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorActionMaps`.
- `WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorActionMapsActions`.
- `WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorActionMapsBalancing`.
- `WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorActionMapsCore`.
- `WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorActionMapsMap`.
- `WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorBalancingExists`.
- `WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorBalancingUnique`.
- `WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorBalancingUniversal`.
- `WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorRelationPresentation`.
- `WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite`.
- `WeilConjectures.AlgebraicGeometry.CoherentCokernelRelations`.
- `WeilConjectures.AlgebraicGeometry.CoherentCokernelRelationsLocal`.
- `WeilConjectures.AlgebraicGeometry.CoherentExtensionRelations`.
- `WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeKernelOver`.
- `WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeSubKernel`.
- `WeilConjectures.AlgebraicGeometry.CoherentHomLocalKernel`.
- `WeilConjectures.AlgebraicGeometry.CoherentIteratedSliceRelations`.
- `WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum`.
- `WeilConjectures.AlgebraicGeometry.CoherentKernelConditionDescent`.
- `WeilConjectures.AlgebraicGeometry.CoherentKernelConditionGluing`.
- `WeilConjectures.AlgebraicGeometry.CoherentKernelConditionRestriction`.
- `WeilConjectures.AlgebraicGeometry.CoherentKernelIntersectionFiniteType`.
- `WeilConjectures.AlgebraicGeometry.CoherentLocalFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.CoherentModuleFiniteTypeLocalCore`.
- `WeilConjectures.AlgebraicGeometry.CoherentModuleFiniteTypeLocalCover`.
- `WeilConjectures.AlgebraicGeometry.CoherentModuleFiniteTypeLocalRestrict`.
- `WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover`.
- `WeilConjectures.AlgebraicGeometry.CoherentSheafHom`.
- `WeilConjectures.AlgebraicGeometry.CohomologyPowersIdealTransitionMaps`.
- `WeilConjectures.AlgebraicGeometry.CokernelTuplePullbackLocalFreeCover`.
- `WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf`.
- `WeilConjectures.AlgebraicGeometry.CompletionAffineSectionsCoordinates`.
- `WeilConjectures.AlgebraicGeometry.CompletionInternalHom`.
- `WeilConjectures.AlgebraicGeometry.CompletionInternalHomAffineCompletionEvaluation`.
- `WeilConjectures.AlgebraicGeometry.CompletionInternalHomAffineComponentwise`.
- `WeilConjectures.AlgebraicGeometry.CompletionInternalHomAffineSectionsLift`.
- `WeilConjectures.AlgebraicGeometry.CompletionInternalHomAffineTensorDictionary`.
- `WeilConjectures.AlgebraicGeometry.CompletionInternalHomQuotient`.
- `WeilConjectures.AlgebraicGeometry.CompletionInternalHomQuotientAnnihilation`.
- `WeilConjectures.AlgebraicGeometry.CompletionInternalHomQuotientIso`.
- `WeilConjectures.AlgebraicGeometry.CompletionInternalHomSectionsLift`.
- `WeilConjectures.AlgebraicGeometry.EpiOverFunctor`.
- `WeilConjectures.AlgebraicGeometry.FiniteTypeEpiImage`.
- `WeilConjectures.AlgebraicGeometry.FiniteTypeKernelLocalGenerators`.
- `WeilConjectures.AlgebraicGeometry.FormalFunctionsPowerKernel`.
- `WeilConjectures.AlgebraicGeometry.FormalModuleQuotientScalarZero`.
- `WeilConjectures.AlgebraicGeometry.GradedCohomologyModuleStructure`.
- `WeilConjectures.AlgebraicGeometry.GradedModuleQuasicoherentRealization`.
- `WeilConjectures.AlgebraicGeometry.GradedModuleRealizationFiniteType`.
- `WeilConjectures.AlgebraicGeometry.GradedModuleRelativeSpecRealization`.
- `WeilConjectures.AlgebraicGeometry.GradedRealizationLocalGeneratorsEpi`.
- `WeilConjectures.AlgebraicGeometry.HomLocalKernelOfPresentation`.
- `WeilConjectures.AlgebraicGeometry.IdealPowerProductRestrictionZero`.
- `WeilConjectures.AlgebraicGeometry.IdealPowerProductZeroAffineCover`.
- `WeilConjectures.AlgebraicGeometry.IdealPowersLocalCoefficientSpan`.
- `WeilConjectures.AlgebraicGeometry.IdealPowersReesGradedData`.
- `WeilConjectures.AlgebraicGeometry.IdealPowersReesMultiplication`.
- `WeilConjectures.AlgebraicGeometry.IdealPowersReesMultiplicationComponent`.
- `WeilConjectures.AlgebraicGeometry.IdealPowersReesZeroGenerators`.
- `WeilConjectures.AlgebraicGeometry.IdentityResolutionHomology`.
- `WeilConjectures.AlgebraicGeometry.InternalHomAffineChartEvaluation`.
- `WeilConjectures.AlgebraicGeometry.InverseImageChangeOfRingsUnitSmul`.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties`.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapCompData`.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapComparison`.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapDataLinearity`.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapSemilinear`.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapZeroAugmentation`.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyScalarEndomorphism`.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison`.
- `WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeImageExtension`.
- `WeilConjectures.AlgebraicGeometry.OpenModuleCohomologyDirectedColimit`.
- `WeilConjectures.AlgebraicGeometry.PushoutRegularModuleComparison`.
- `WeilConjectures.AlgebraicGeometry.QcqsCohomologyDirectSum`.
- `WeilConjectures.AlgebraicGeometry.QcqsCohomologyFiniteSubsumRepresentatives`.
- `WeilConjectures.AlgebraicGeometry.QcqsCohomologySmallSubsumDiagram`.
- `WeilConjectures.AlgebraicGeometry.QuasiCoherenceScalarRestriction`.
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraAffineInclusion`.
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraChangeOfRings`.
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover`.
- `WeilConjectures.AlgebraicGeometry.QuasicoherentSheafHom`.
- `WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal`.
- `WeilConjectures.AlgebraicGeometry.RelativeSpecMorphismChart`.
- `WeilConjectures.AlgebraicGeometry.RelativeSpectrumAffineRealization`.
- `WeilConjectures.AlgebraicGeometry.RelativeSpectrumStructureAlgebra`.
- `WeilConjectures.AlgebraicGeometry.RestrictionNaturality`.
- `WeilConjectures.AlgebraicGeometry.SheafTensorPushoutCancellation`.
- `WeilConjectures.AlgebraicGeometry.SheafTensorPushoutComparisonIsIso`.
- `WeilConjectures.AlgebraicGeometry.TensorRelationSectionQuotient`.
- `WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyAgree`.
- `WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural`.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural`.
- `WeilConjectures.CategoryTheory.RightDerivedExactComposite`.
- `WeilConjectures.RingTheory.FiniteModuleComplete`.
- `WeilConjectures.Topology.InverseImageRegularExtension`.
- `WeilConjectures.Topology.InverseImageRegularModule`.

Existing DAG nodes attached to those removed modules (also local to this item):

- `aux-closed-immersion-ideal-power-annihilation`.
- `def-weil-pbc-coherent-thickening-system`.
- `def-weil-pbc-comm-algebra-sheaf`.
- `lem-sc-module-cohomology-source-comparison`.
- `lem-stage3-epi-over-functor`.
- `lem-weil-pbc-adic-completion-stable-ranges`.
- `lem-weil-pbc-affine-algebra-local-maps`.
- `lem-weil-pbc-affine-algebra-module-generators`.
- `lem-weil-pbc-affine-base-change-sections-induction`.
- `lem-weil-pbc-affine-basis-ring-action-gluing`.
- `lem-weil-pbc-affine-morphism-cohomology-edge`.
- `lem-weil-pbc-affine-pushforward-ideal-product`.
- `lem-weil-pbc-affine-structure-algebra-fully-faithful`.
- `lem-weil-pbc-balanced-action-affine-open`.
- `lem-weil-pbc-balanced-action-affine-sections`.
- `lem-weil-pbc-balanced-action-direct-image-module`.
- `lem-weil-pbc-change-of-rings-tensor-action-maps-actions`.
- `lem-weil-pbc-closed-immersion-power-quotient`.
- `lem-weil-pbc-closed-immersion-unit-quotient`.
- `lem-weil-pbc-coherent-hom-local-kernel-from-presentation`.
- `lem-weil-pbc-coherent-kernel-condition-descent`.
- `lem-weil-pbc-coherent-kernel-condition-descent-local-generators`.
- `lem-weil-pbc-coherent-kernel-condition-restriction`.
- `lem-weil-pbc-coherent-kernel-intersection-finite-type`.
- `lem-weil-pbc-coherent-sheaf-hom-coherent`.
- `lem-weil-pbc-cohomology-powers-ideal-application`.
- `lem-weil-pbc-cohomology-powers-ideal-application-image`.
- `lem-weil-pbc-cohomology-powers-ideal-application-kernel`.
- `lem-weil-pbc-cohomology-powers-ideal-application-transition-maps`.
- `lem-weil-pbc-cohomology-powers-ideal-rees-finite`.
- `lem-weil-pbc-completion-from-restriction`.
- `lem-weil-pbc-completion-internal-hom`.
- `lem-weil-pbc-finite-module-complete-over-complete-noetherian`.
- `lem-weil-pbc-finite-rees-module-single-degree-generation`.
- `lem-weil-pbc-formal-completion-fully-faithful-proper`.
- `lem-weil-pbc-formal-completion-map-injective-proper`.
- `lem-weil-pbc-formal-completion-map-surjective-proper`.
- `lem-weil-pbc-formal-functions-complete-base`.
- `lem-weil-pbc-formal-functions-power-kernel`.
- `lem-weil-pbc-graded-cohomology-module-finite`.
- `lem-weil-pbc-graded-cohomology-module-finite-generators`.
- `lem-weil-pbc-graded-cohomology-module-structure`.
- `lem-weil-pbc-graded-finiteness-cohomology`.
- `lem-weil-pbc-graded-module-relative-spec-realization`.
- `lem-weil-pbc-grothendieck-existence-supported-hom`.
- `lem-weil-pbc-ideal-module-product-stalk`.
- `lem-weil-pbc-ideal-power-product-restriction-zero`.
- `lem-weil-pbc-ideal-power-product-zero-affine-cover`.
- `lem-weil-pbc-ideal-powers-rees-graded-data`.
- `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`.
- `lem-weil-pbc-ml-cohomology-powers-ideal`.
- `lem-weil-pbc-module-cohomology-fmap-functorial`.
- `lem-weil-pbc-module-cohomology-scalar-endomorphism`.
- `lem-weil-pbc-module-pullback-finite-type`.
- `lem-weil-pbc-qcqs-cohomology-direct-sum`.
- `lem-weil-pbc-quasi-coherent-finite-type-affine`.
- `lem-weil-pbc-quasi-coherent-module-cokernel-image`.
- `lem-weil-pbc-quotient-base-change-closed-immersion-ideal`.
- `lem-weil-pbc-rees-kernel-bounded-generators`.
- `lem-weil-pbc-relative-spec-morphism-chart`.
- `lem-weil-pbc-relative-spectrum-structure-algebra`.
- `lem-weil-pbc-sheaf-finite-type-epi-image`.
- `lem-weil-pbc-sheaf-hom-finite-presentation-quasi-coherent`.
- `lem-weil-pbc-theorem-formal-functions`.
- `lem-weil-pbc-thickening-completion-hom-dictionary`.
- `lem-weil-pbc-thickening-system-comparison-transport`.
- `lem-weil-pbc-thickening-system-hom-transport`.
- `lem-weil-pbc-thickening-system-hom-transport-core`.
- `lem-weil-pbc-thickening-system-pushforward-adic`.
- `lem-weil-pbc-thickening-system-pushforward-functor`.
- `lem-weil-pbc-thickening-system-pushforward-lifting`.
- `lem-weil-pbc-thickening-system-pushforward-lifting-assembly`.
- `lem-weil-pbc-thickening-system-pushforward-lifting-termwise`.
- `lem-weil-pbc-thickening-systems-completion-comparison`.
- `lem-weil-pbc-thickening-systems-dictionary`.
- `lem-weil-pbc-thickening-systems-pushforward-equivalence`.
- `ml-cohomology-powers-ideal-image-stabilization`.
- `ml-cohomology-powers-ideal-kernel-bound`.

## Where the brief, the DAG or earlier work was wrong

The existing DAG's second step referred to private ideal-power helpers through
`Sheaf.AlgebraicGeometry.IdealPowerProductRestrictionZero`. The current source has
retired that module to a re-export of its upstream counterpart, while the last green
compiled snapshot still exposes the old helpers. Depending on that obsolete private
interface could pass the local compile and fail after the source sync. The delivered
proof uses only public APIs and avoids that discrepancy.

The earlier endpoint-transport dependency imported proper-completion theory although
the argument only needs elementary functor and isomorphism laws. That import and its
unnecessary descendants are removed. No mathematical statement was disputed or
changed. No change record is required because the public interface is unchanged.


## Second reading by S2

1. **Interface preservation — pass.** Read the complete module and its diff against
   the shared repository. Independently compared the complete signatures of all four
   existing theorems, including private visibility: byte-identical. The original two
   public imports and all docstrings are unchanged. There are no definitions, new
   declarations, adapted modules, or statement changes in this delivery.
2. **Proof and trust — pass.** Independently compiled the delivered module with
   `lcompile.py --all`. A fresh scratch copy printing axioms of all four declarations
   reports only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Checked that the source contains no `sorry`, forbidden proof constructs, or lines
   exceeding 100 characters. The support bridge identifies the two power ideals by
   their affine section images and uses tensor-section surjectivity and affine-basis
   sheaf separatedness correctly. The component lifts are uniquely determined by
   injectivity, and adjacent compatibility is the naturality equation with the
   correct source and target indices. No data comes from an unproved theorem.
3. **Split statements — pass, none.** There are no new statements, new nodes, or
   residual holes to check or close. Reviewed zero modules, the zero and unit ideals,
   and the empty scheme: the positive common exponent and affine-basis argument
   require no nonemptiness or properness assumption. Read the actual Stacks source,
   `coherent.tex`, lemma-existence-tricky (Tag 088A), including the use of closed
   pushforward and the construction of the maps to H/K^e H.
4. **Route and pruning — pass.** Independently searched local Sheaf and upstream
   modules for supported completion, annihilation, and Hom bijections; ran Mathlib
   grep for isomorphism transport and sequence transformations, and Loogle for
   `CategoryTheory.Iso.homCongr`. Loogle supplied `Functor.map_homCongr`, used below.
   The remaining proof uses existing public declarations; the removed private
   endpoint helper would require the unnecessary proper-completion import. All
   proof imports are private and supply the APIs used in the proof; no additional
   geometric assumption is introduced. Recomputed both source import closures and
   checked that the report lists exactly all 196 removed modules. The sole removed
   old proof dependency is the listed ideal-power restriction node. Read
   `dag/units/sk-thm-p1.json`: its statement, steps, and realized nodes are preserved;
   this proof changes only the route below that level.
5. **DAG agreement — pass.** Compared the node JSON against the repository:
   only `proof`, `proof_deps`, and `proof_origin` differ. Read every cited node's
   statement and Lean declaration and checked their use in the proof. The new
   dependency list is exactly the union of the steps' `uses`; the old restriction
   dependency is removed. No new-node fields or change record are required.

Second-reading change: replaced the elementary reproof of functor compatibility
with `Iso.homCongr` by the existing Mathlib theorem `T.map_homCongr a b w`.
No other Lean or node edits were needed. Added this independent review to the report.
The delivery still closes both original holes and adds none.
