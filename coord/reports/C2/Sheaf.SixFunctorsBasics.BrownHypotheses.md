## What changed

Reprove coefficient-isomorphism invariance by the exact derived equivalence restricted to
the localizing full subcategories, using the adopted source's IsCompactObj.of_adjunction.
A private proved minimality helper establishes preservation of the localizing closures.
The invariant theorem and its private helpers now live in
Sheaf.SixFunctorsBasics.BrownHypothesesCoefficientIso, which imports the general criteria.
Its old CondensedCoefficientIsoConstructible proof import also leaves the item.
Remove the old ambient-Hom transport helper and the private proof imports of
Sheaf.Paper.BrownHypothesesGeneration and
Sheaf.SixFunctorsBasics.BrownHypothesesArbitraryFieldCompactness.

Move the already proved CategoryTheory.brownHypotheses_of_finiteFieldDatum, with its exact
statement, docstring and proof, to Sheaf.SixFunctorsBasics.BrownHypothesesFiniteField.
The general criteria no longer import geometric finite-field compactness theory.
Move their unneeded public FiniteFieldFiber import to the finite-field specialization,
whose statement is the only moved statement that names a finite-field datum.
Update the affected node records and attach the existing source adjunction lemma to
one new node.
Change record: coord/changes/C2-brown-specialization-import-pruning.md.

## Proved and sorry left

Holes closed: 0 of 1. Holes added: 0. Split-off sorry statements: 0.
The single remaining hole is CategoryTheory.brownHypotheses,
node sk-lem-brown-hypotheses; its signature and body remain unchanged.
CategoryTheory.brownHypothesesFor_coefficientIso_iff has a new complete proof in its new
coefficient-isomorphism module;
CategoryTheory.brownHypotheses_of_finiteFieldDatum keeps its complete proof at its new
module. The private minimality helper is completely proved. This is a pruning delivery,
not a proof or decomposition of the disputed arbitrary-field assertion.

Validation: all three delivered Lean modules and both unchanged direct importers passed
remote compilation within the enforced per-file limit. The unchanged validation copies
were removed from the sandbox. No consumer is adapted. The packet contains exactly the
original hole.

## No longer needed

The coefficient-isomorphism argument no longer needs the private ambientCompactness_of_full,
localizingClosure_coproduct, compactness_coefficientIso, or compactness_of_fullyFaithful
helpers from Sheaf.Paper.BrownHypothesesGeneration. It uses equivalences and the source
compact-object adjunction lemma instead. The general criterion module no longer needs the
finite-field compactness helper, which is imported only by the separate specialization.
No public declaration or module is withdrawn, and every existing public theorem is preserved.
The old private ambient-compactness helper is removed after replacing its unique caller.

Source-graph census at the original delivery's preparation: 228 project modules left the
item's import closure, including 105 modules then in the TargetsCheck closure.
No new module enters that original target closure.
Mathlib modules are excluded. These are source import-graph counts, not the independently
pinned sorry ledger. On the current checkout, including archived sources, the item still
loses 228 imports. The updated TargetsCheck no longer reaches the item, so this repair has
no additional effect on its present closure. The following 105-module list records the
original target-closure pruning:

- Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
- Sheaf.Algebra.Homology.LocallyFreeDerivedScalars
- Sheaf.Algebra.Homology.SubcategoryRightResolution
- Sheaf.Algebra.Homology.SubcategoryRightResolutionSystem
- Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension
- Sheaf.AlgebraicGeometry.BaseFieldFiniteTorsionCohomologicalDimension
- Sheaf.AlgebraicGeometry.CohomologicalDimension
- Sheaf.AlgebraicGeometry.EllCohomologicalDimensionComparison
- Sheaf.AlgebraicGeometry.EtaleModuleAffineBound
- Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison
- Sheaf.AlgebraicGeometry.FiniteDiscreteCtfOrigin
- Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact
- Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
- Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizer
- Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizerOpenIndex
- Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizerRange
- Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
- Sheaf.AlgebraicGeometry.IsRegularScheme
- Sheaf.AlgebraicGeometry.ModuleCohomologyConventions
- Sheaf.AlgebraicGeometry.ProEtaleClassicalBounds
- Sheaf.AlgebraicGeometry.ProEtaleModuleObjectProductsExact
- Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts
- Sheaf.AlgebraicGeometry.Sites.AffineLimitSheafApproximation
- Sheaf.AlgebraicGeometry.Sites.AffineLimitSheafApproximationEpi
- Sheaf.AlgebraicGeometry.Sites.AffineLimitSheafApproximationGermKernel
- Sheaf.AlgebraicGeometry.Sites.AffineLimitSheafReconstruction
- Sheaf.AlgebraicGeometry.Sites.FiniteFieldTorsionCohomologicalDimension
- Sheaf.AlgebraicGeometry.Sites.HigherDirectImageAffineEtaleBound
- Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit
- Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison
- Sheaf.AlgebraicGeometry.UnboundedDirectImageTruncationStability
- Sheaf.AlgebraicGeometry.UnboundedSiteComparison
- Sheaf.CategoryTheory.ExactLocalizationDerivedTriangle
- Sheaf.CategoryTheory.Galois.AutProfinite
- Sheaf.Paper.BrownHypothesesGeneration
- Sheaf.Paper.ConstructibleCompactness
- Sheaf.Paper.ConstructibleCompactnessBounded
- Sheaf.Paper.ConstructibleIndExtBound
- Sheaf.Paper.DetIndHeartIISums
- Sheaf.Paper.FiniteComparisonFaithful
- Sheaf.Paper.FiniteComparisonLocalizing
- Sheaf.Paper.FiniteConstantModelStrataGeneration
- Sheaf.Paper.FiniteConstantModelsCommonStratification
- Sheaf.Paper.FiniteWindow
- Sheaf.Paper.FiniteWindowUnbounded
- Sheaf.Paper.FormalClosedSupportII
- Sheaf.Paper.GaloisLisseCorrespondenceData
- Sheaf.Paper.IntegralConstantModelLocalResolution
- Sheaf.Paper.IntegralConstructibleExt
- Sheaf.Paper.IntegralConstructibleReductionLimit
- Sheaf.Paper.IntegralDualTorsionHeartSections
- Sheaf.Paper.IntegralHeartLocalDualityDescent
- Sheaf.Paper.IntegralReductionSupportAmplitude
- Sheaf.Paper.IntegralStratumExtBound
- Sheaf.Paper.IntegralStratumHomFormula
- Sheaf.Paper.IntegralStratumReductionExtBound
- Sheaf.Paper.LatticeSupportedHomFiniteComparison
- Sheaf.Paper.LisseAdicFiberFunctors
- Sheaf.Paper.LisseAdicSheaves
- Sheaf.Paper.LisseCoefficientFiberComparisons
- Sheaf.Paper.LisseCoefficientFiberEndomorphisms
- Sheaf.Paper.LisseFiberCoherenceNormalization
- Sheaf.Paper.LisseIntegralScalarFiberIsomorphism
- Sheaf.Paper.LisseIntegralSmallCoefficients
- Sheaf.Paper.LisseQlbarRepresentationDefs
- Sheaf.Paper.LisseRationalScalarFiberMaps
- Sheaf.Paper.LisseScalarFiberMaps
- Sheaf.Paper.LisseScalarFiberReductions
- Sheaf.Paper.LisseTensorScalarExtension
- Sheaf.Paper.NormalLisseFiniteCoefficientLattice
- Sheaf.Paper.NormalizedFibreComparisons
- Sheaf.Paper.SupportedLatticeHomReductionTower
- Sheaf.Paper.UniformConstructibleExt
- Sheaf.Paper.UniformConstructibleExtIntegral
- Sheaf.Paper.UniformConstructibleExtRational
- Sheaf.Paper.UniformConstructibleExtTorsion
- Sheaf.RepresentationTheory.LAdic
- Sheaf.SixFunctors.ClosedImmersionTensorProjection
- Sheaf.SixFunctors.FiniteCompactProetale
- Sheaf.SixFunctors.IntTensorProjection
- Sheaf.SixFunctors.ScalarSixGeometry
- Sheaf.SixFunctors.ScalarSixImmersionComparison
- Sheaf.SixFunctors.ScalarSixNormalizedImmersion
- Sheaf.SixFunctors.ScalarSixOpenComparison
- Sheaf.SixFunctors.ScalarSixPullback
- Sheaf.SixFunctorsBasics.BrownHypothesesArbitraryFieldCompactness
- Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness
- WeilConjectures.Algebra.Homology.SubcategoryRightResolutionAssembly
- WeilConjectures.AlgebraicGeometry.Curve.FiniteStalkSubobjectElement
- WeilConjectures.AlgebraicGeometry.Curve.FiniteStalkSubobjectsCover
- WeilConjectures.AlgebraicGeometry.Curve.GenericFinitePrimaryDecomposition
- WeilConjectures.AlgebraicGeometry.EtaleSheafDiscreteContinuousRep
- WeilConjectures.AlgebraicGeometry.GaloisPointGeometricComparison
- WeilConjectures.AlgebraicGeometry.Sites.GaloisModule
- WeilConjectures.CategoryTheory.Sites.Point.DiscreteModule
- WeilConjectures.CategoryTheory.Sites.Point.GroupAction
- WeilConjectures.Mathlib.FieldTheory.KrullTopology
- WeilConjectures.RepresentationTheory.DiscreteContinuousRep
- WeilConjectures.RepresentationTheory.DiscreteModule.Basic
- WeilConjectures.RepresentationTheory.DiscreteModule.CohomologicalDimension
- WeilConjectures.RepresentationTheory.DiscreteModule.DiscreteContinuousRep
- WeilConjectures.RepresentationTheory.DiscreteModule.Induction
- WeilConjectures.RepresentationTheory.DiscreteModule.Sylow
- WeilConjectures.RepresentationTheory.DiscreteModule.Transport
- WeilConjectures.RepresentationTheory.FinitePrimaryDecomposition

The further modules leaving only the item's closure (still reached by other target routes) are:

- Sheaf.Algebra.Homology.KFlatRoosRepresentativeInvariance
- Sheaf.Algebra.Homology.RingedFlatSingleTensorCohomology
- Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction
- Sheaf.Algebra.Homology.StrictScalarHomChain
- Sheaf.AlgebraicGeometry.AffineEtaleFreeDetection
- Sheaf.AlgebraicGeometry.ComparisonTorInterval
- Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality
- Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom
- Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps
- Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization
- Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula
- Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
- Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
- Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel
- Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
- Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators
- Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
- Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction
- Sheaf.AlgebraicGeometry.IntrinsicResolutionTensorComparison
- Sheaf.AlgebraicGeometry.IntrinsicTorAmplitudeTransport
- Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits
- Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk
- Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk
- Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk
- Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence
- Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension
- Sheaf.CategoryTheory.CompactObject
- Sheaf.CategoryTheory.LocallyPrescribedModulesSmall
- Sheaf.CategoryTheory.ProjectionInternalHom
- Sheaf.CategoryTheory.RegularScalarExtensionMultiplication
- Sheaf.CategoryTheory.RightDerivedFunctorUpperBound
- Sheaf.Paper.AmbientIndDerivedSums
- Sheaf.Paper.AmbientIndDerivedTriangulated
- Sheaf.Paper.CoefficientFiniteDescentHom
- Sheaf.Paper.CoefficientFiniteDescentLisse
- Sheaf.Paper.CompletedFreeCellOrdinaryLimit
- Sheaf.Paper.CondensedCoefficientComparisons
- Sheaf.Paper.CondensedFlatCoefficientCalculus
- Sheaf.Paper.CondensedPointModuleComparison
- Sheaf.Paper.FiniteCoefficientDescentTwoColimit
- Sheaf.Paper.FiniteCtfTriangulated
- Sheaf.Paper.FiniteModelFreeComplexReduction
- Sheaf.Paper.FiniteModelOrdinaryFreeComplex
- Sheaf.Paper.FiniteModelOrdinaryScalar
- Sheaf.Paper.FiniteModelQuotientChartComparison
- Sheaf.Paper.FiniteModelQuotientCohomologyDescent
- Sheaf.Paper.FiniteModelSheafQuotientConstructible
- Sheaf.Paper.FiniteModelSheafQuotientData
- Sheaf.Paper.FiniteModelStratumFiltration
- Sheaf.Paper.FiniteScalarLocalModelComplete
- Sheaf.Paper.FiniteStrataCompletionDetection
- Sheaf.Paper.FormalClosedSupport
- Sheaf.Paper.FormalClosedSupportDerived
- Sheaf.Paper.FormalClosedSupportSheaves
- Sheaf.Paper.IntegralCoefficientQuotientLimit
- Sheaf.Paper.IntegralModelSurjectiveClosedReflection
- Sheaf.Paper.IntegralScalarModelCoordinates
- Sheaf.Paper.IntegralTensorShriek
- Sheaf.Paper.IntrinsicRealizationFlat
- Sheaf.Paper.IntrinsicRealizationOriginComparison
- Sheaf.Paper.LisseFiniteCoefficientModel
- Sheaf.Paper.LisseFiniteHomLift
- Sheaf.Paper.ProEtaleFixedModuleConstructible
- Sheaf.Paper.ProEtaleScalarLocalModelRepresentatives
- Sheaf.Paper.ProperHeartBoundTorsion
- Sheaf.Paper.PurEtaleClosedRightAdjointCoproducts
- Sheaf.Paper.PurEtaleLisseDualizable
- Sheaf.Paper.PurEtaleLisseStratumCompact
- Sheaf.Paper.QcqsIntegralFiniteModelCompleteness
- Sheaf.Paper.ReducedSourceFactors
- Sheaf.Paper.StrictCompletionFiniteConstantModels
- Sheaf.Paper.StrictCompletionRestrictionComparison
- Sheaf.Paper.StrictCompletionRestrictionData
- Sheaf.Paper.StrictCompletionRestrictionLimits
- Sheaf.Paper.StrictIntegralCompletionPresentation
- Sheaf.Paper.StrictIntegralScalarPullback
- Sheaf.Paper.StrictScalarCompletionFunctorComparison
- Sheaf.Paper.StrictSectionPrincipalQuotientModels
- Sheaf.Paper.StrictSectionQuotientConeMaps
- Sheaf.Paper.StrictSectionQuotientTensorModels
- Sheaf.Paper.StrictSectionScalarPresentation
- Sheaf.SixFunctors.CompletedCoefficientFreeResolution
- Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison
- Sheaf.SixFunctors.FlatModel
- Sheaf.SixFunctors.FlatModelGeneration
- Sheaf.SixFunctors.OpenClosedFlatness
- Sheaf.SixFunctors.OpenImmersionTensorProjection
- Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
- WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimit
- WeilConjectures.AlgebraicGeometry.ProEtale.CohomologyFilteredColimit
- WeilConjectures.CategoryTheory.RingObjects.GlobalSections
- WeilConjectures.CategoryTheory.Sites.PullbackIsoOfLocallyGenerated
- WeilConjectures.CategoryTheory.Sites.SheafComposeBraided
- WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
- WeilConjectures.CategoryTheory.Sites.SheafSmul
- WeilConjectures.CategoryTheory.Triangulated.TStructure.Karoubian
- WeilConjectures.Mathlib.CategoryTheory.Idempotents.Basic
- WeilConjectures.Mathlib.CategoryTheory.Limits.Constructions.Filtered
- WeilConjectures.Mathlib.CategoryTheory.Monoidal.Conv
- WeilConjectures.Mathlib.CategoryTheory.Preadditive.Biproducts
- WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafForgetAb
- WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafPadicInt
- WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafPadicIntExtendScalars
- WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
- WeilConjectures.SixFunctors.ProEtale.Adic.ForgetAbRightDerivedLowerStar
- WeilConjectures.SixFunctors.ProEtale.Adic.ForgetLaxMonoidal
- WeilConjectures.SixFunctors.ProEtale.Adic.ForgetMonoidalAdjunction
- WeilConjectures.SixFunctors.ProEtale.Adic.FreeWeilCoefficients
- WeilConjectures.SixFunctors.ProEtale.Adic.Module
- WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafComparison
- WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafIso
- WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafRing
- WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntExtendScalars
- WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleExtendScalarsBaseChange
- WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRationalization
- WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRationalizationRegular
- WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRightDerivedLowerStar
- WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleUpperStar
- WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit
- WeilConjectures.SixFunctors.ProEtale.Adic.Ring
- WeilConjectures.SixFunctors.ProEtale.Adic.UpperStar
- WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
- WeilConjectures.SixFunctors.ProEtale.LowerStarFilteredColimit

All corresponding DAG attachments in modules leaving the item's Lean import closure are:

- a4-brown-finite-field-internal-compactness
- def-exc-discrete-modules-category
- def-pod-galois-correspondence-data-e4
- def-pod-l-adic-representations
- def-pod-lisse-adic-fibre-functors
- def-pod-lisse-l-adic-sheaves
- def-sc-affine-limit-sheaf-approximation
- def-sf-completed-coefficient-free-cell
- def-sfb-finite-model-quotient-coordinates
- def-sfb-integral-model-condensed-coefficients
- def-sfb-lisse-representation-data
- def-sfb-open-closed-internal-hom-comparisons
- def-sfb-set-functor-aut-pointwise-topology
- def-sfb-strict-completion-restriction-data
- def-weil-pbc-condensed-coefficient-comparisons
- def-weil-pbc-etale-origin-witness
- def-weil-proetale-constructible-sheaf
- def-weil-regular-scheme
- det-ambient-ind-derived-sums
- det-ambient-ind-derived-triangulated
- det-base-field-cd-finite-torsion-bound
- det-brown-hypotheses-generation
- det-cd-etale-comparison
- det-constructible-compactness-bounded
- det-ctf-finite-compact-etale
- det-ctf-finite-compact-proetale
- det-ctf-finite-comparison-localizing
- det-finite-window-unbounded
- det-ind-heart-ii-sums
- det-lem-coefficient-finite-descent-hom
- det-lem-coefficient-finite-descent-lisse
- det-lem-formal-closed-support-derived
- det-lem-formal-closed-support-sheaves
- det-lem-int-ext-bound
- det-lem-int-ext-formula
- det-lem-int-tensor-projection
- det-lem-int-tensor-shriek
- det-pbc-conventions-module-cohomology
- det-pe-unbounded-classical-bounds
- det-prop-scalar-six-pullback
- det-proper-heart-bound-torsion
- det-sf-flat-model-generation
- det-sf-open-closed-extension-zero-limits
- det-sf-open-closed-pullback-limits
- det-uniform-constructible-ext-integral
- det-uniform-constructible-ext-rational
- det-uniform-constructible-ext-torsion
- lem-cbc-proetale-classical-stalk
- lem-cbc-proetale-comparison-stalk
- lem-ctf-finite-comparison-generators
- lem-ctf-finite-comparison-ordinary-fully-faithful
- lem-etale-derived-functor-upper-amplitude
- lem-exc-closed-ambient
- lem-exc-closed-support-triangle
- lem-exc-comparison-tor-interval
- lem-exc-intrinsic-resolution-tensor-homology
- lem-exc-intrinsic-tor-amplitude-transport
- lem-fd-ringed-flat-single-tensor-cohomology
- lem-finite-constant-model-fixed-strata-generation
- lem-finite-constant-models-common-reduced-stratification
- lem-finite-discrete-ctf-origin
- lem-finite-window-ind-ext-bound
- lem-galois-aut-profinite
- lem-galois-pi1-finite-etale-image-stabilizer
- lem-galois-pi1-finite-etale-image-stabilizer-open-index
- lem-galois-pi1-finite-etale-image-stabilizer-range
- lem-integral-constant-model-local-resolution
- lem-integral-heart-local-duality-descent
- lem-pe-higher-direct-image-filtered-colimits
- lem-pe-kflat-roos-representative-invariance
- lem-pod-etale-stalk-tensor-scalar
- lem-pod-lisse-coefficient-fiber-comparisons
- lem-pod-lisse-coefficient-fiber-endomorphisms
- lem-pod-lisse-fiber-coherence-normalization
- lem-pod-lisse-integral-scalar-fiber-isomorphism
- lem-pod-lisse-integral-scalar-fiber-map
- lem-pod-lisse-rational-scalar-fiber-comparison
- lem-pod-lisse-scalar-fiber-reductions
- lem-pod-lisse-tensor-and-scalar-extension
- lem-pur-affine-etale-free-detection
- lem-pur-etale-closed-right-adjoint-coproducts
- lem-pur-etale-finite-ring-compact-generators
- lem-pur-etale-lisse-dualizable
- lem-pur-etale-lisse-stratum-compact
- lem-pur-proetale-inverse-image-stalk
- lem-route-formal-closed-support-adjunction
- lem-sc-affine-limit-sheaf-approximation-epi
- lem-sc-affine-limit-sheaf-approximation-germ-kernel
- lem-sc-affine-limit-sheaf-reconstruction
- lem-sc-cd-affine-limit
- lem-sc-field-finite-stalk-subobject-element
- lem-sc-field-torsion-finite-stalk-subobjects-cover
- lem-sc-finite-discrete-rep-primary-decomposition
- lem-sc-generic-finite-primary-decomposition
- lem-sf-completed-coefficient-free-resolution
- lem-sf-completed-free-cell-ordinary-limit
- lem-sf-etale-flat-constructible
- lem-sf-exact-localization-derived-triangle
- lem-sf-integral-constructible-reduction-limit
- lem-sf-integral-dual-torsion-heart-sections
- lem-sf-integral-reduction-support-amplitude
- lem-sf-integral-stratum-reduction-ext-bound
- lem-sf-intrinsic-realization-flat
- lem-sf-intrinsic-realization-origin-comparison
- lem-sf-native-adic-pullback-exact-lisse
- lem-sf-proetale-module-object-products-exact
- lem-sf-separably-closed-torsion-cd
- lem-sfb-closed-immersion-derived-tensor-projection
- lem-sfb-condensed-support-derived-localization
- lem-sfb-condensed-support-projection-formula
- lem-sfb-etale-locally-closed-extension-comparison
- lem-sfb-etale-module-affine-bound
- lem-sfb-finite-classical-unbounded-comparison
- lem-sfb-finite-field-all-torsion-cd
- lem-sfb-finite-model-free-complex-reduction
- lem-sfb-finite-model-ordinary-free-complex
- lem-sfb-finite-model-ordinary-scalar
- lem-sfb-finite-model-quotient-chart-comparison
- lem-sfb-finite-model-quotient-cohomology-descent
- lem-sfb-finite-model-sheaf-quotient-constructible
- lem-sfb-finite-model-stratum-filtration
- lem-sfb-finite-scalar-local-model-complete
- lem-sfb-finite-strata-completion-detection
- lem-sfb-higher-direct-image-affine-etale-bound
- lem-sfb-hom-scalar-chain-identification
- lem-sfb-integral-coefficient-quotient-limit
- lem-sfb-integral-model-surjective-closed-reflection
- lem-sfb-integral-scalar-model-coordinates
- lem-sfb-lattice-supported-hom-finite-comparison
- lem-sfb-lattice-supported-hom-reduction-tower
- lem-sfb-lisse-finite-coefficient-model
- lem-sfb-lisse-finite-hom-lift
- lem-sfb-locally-free-derived-scalars
- lem-sfb-locally-prescribed-modules-small
- lem-sfb-normal-lisse-finite-coefficient-lattice
- lem-sfb-open-closed-flatness
- lem-sfb-open-closed-internal-hom-formulas
- lem-sfb-open-immersion-derived-tensor-projection
- lem-sfb-proetale-scalar-local-model-representatives
- lem-sfb-projection-internal-hom-formal
- lem-sfb-qcqs-integral-finite-model-completeness
- lem-sfb-regular-scalar-extension-multiplication
- lem-sfb-scalar-six-geometry
- lem-sfb-scalar-six-immersion-comparison
- lem-sfb-scalar-six-normalized-immersion
- lem-sfb-scalar-six-open-comparison
- lem-sfb-slice-scalar-hom-chain-adjunction
- lem-sfb-strict-completion-finite-constant-models
- lem-sfb-strict-completion-restriction-comparison
- lem-sfb-strict-completion-restriction-limits
- lem-sfb-strict-integral-completion-presentation
- lem-sfb-strict-integral-scalar-pullback
- lem-sfb-strict-scalar-completion-functor-comparison
- lem-sfb-strict-section-principal-quotient-models
- lem-sfb-strict-section-quotient-cone-maps
- lem-sfb-strict-section-quotient-tensor-models
- lem-sfb-strict-section-scalar-presentation
- lem-sfb-unbounded-direct-image-comparison
- lem-sfb-unbounded-direct-image-truncation-stability
- lem-sfb-unbounded-site-comparison
- lem-trf-proetale-pullback-stalk-coherence
- lem-weil-finite-ctf-triangulated
- lem-weil-pbc-complex-injective-resolution-mono
- lem-weil-pbc-condensed-flat-coefficient-calculus
- lem-weil-pbc-subcategory-right-resolution-05T6
- lem-weil-pbc-subcategory-right-resolution-assembly
- lem-weil-pbc-subcategory-right-resolution-system
- lem-zl-condensed-lisse-proetale-locality
- lem-zl-condensed-point-module-comparison
- new-e5-normalized-fibre-comparisons
- p3-brown-finite-field-object-compactness
- p3-brown-integral-object-compactness-with-ext-bound
- sk-def-cd
- sk-lem-base-field-cd
- sk-lem-finite-window
- sk-lem-formal-closed-support
- sk-lem-formal-closed-support-ii
- sk-lem-int-ext
- sk-lem-sf-flat-model
- sk-lem-uniform-constructible-ext
- sk-thm-constructible-compactness
- sk-thm-sfb-qlbar-two-colimit
- thm-galois-fundamental
- thm-galois-lc-etale

These nodes are retained: unfinished DAG parents and the finite-field specialization may
still need them. This packet does not claim permission to withdraw their modules.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the original Brown theorem lacks a finiteness assumption on the base
field. Its existing comment explains the infinite-transcendence-degree field obstruction.
The current blueprint still asserts the general claim, but the finite-field compactness
dependencies require the geometric field of a finite-field datum, and the integral theorem
requires an explicit uniform constructible Ext bound. The maintainer's
coord/changes/maintenance-K4-brown-false-split-rollback.md says to keep the original hole,
not recreate the false unrestricted compactness splits, and await a human correction of
the unit statement. This delivery respects that instruction and adds no such assumption.

The earlier coefficient proof imported geometric finite-field theory just to use generic
private Hom-transport helpers. The existing source adjunction lemma removes that coupling.
A full dependency traversal also encounters the unchanged baseline cycle
lemma-weil-pbc-derived-exchange-replacement → lem-weil-pbc-derived-exchange-termwise →
lem-weil-pbc-derived-exchange-bounded-comparison → lemma-weil-pbc-derived-exchange-replacement.
This packet does not change those nodes or edges.
The unit's statement and proof steps are unchanged. The finite-field specialization is
preserved with all its hypotheses; it is not substituted for the disputed general claim.

## New nodes

lem-sfb-compact-object-adjunction attaches the already proved
CategoryTheory.BrownRepresentability.IsCompactObj.of_adjunction in
WeilConjectures.CategoryTheory.Triangulated.CompactBoundedHom. It introduces no declaration,
module or hole. Its proof transposes a map to a coproduct, uses finite support, and
transposes the finite family back. Both categories use the same Hom/indexing universe;
no all-coproduct-existence assumption is added to the original source theorem.
Blueprint and DAG searches found no existing node for this generic source theorem.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
