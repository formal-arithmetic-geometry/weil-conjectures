## What changed

Retained the previous sandbox and continued proofs in `Sheaf.Paper.PbcScalarExtension`.
The coefficient-kernel proof transports the unlifted quotient-kernel theorem through
ULift using divisibility. The completed coefficient map is the limit map of the
residue maps; its uniqueness follows from the limit projections. Coefficient-map
composition and identity use the same uniqueness. Restriction identity is fixed
sectionwise. Rational Hom functor laws use the prescribed pure-tensor formula,
ring-hom laws and tensor induction. Rational unit and associator naturality reduce
by the same tensor induction to the existing ambient naturality equations.

The triangulation adapters project the published witness. Ambient associator
naturality uses two adjunction transpositions and unit naturality. Subfield
inclusions are extensional identities. Stage exactness transports through the
specified normalization and its shift. Conditional restriction inherits linearity;
localization of the ambient exchange equality gives rational completed exchange.
The primary coherent scalar-extension theorem combines its existing companion
exactness, unit, pentagon and shift statements. The resumed work additionally proves rational scalar shift uniqueness, rational
exactness, rational direct-image and completed-pullback comparison uniqueness, and
completion coherence for successive coefficient extensions. Ambient exactness
descends the normalized Kan counit on K-flat resolutions; raw scalar localization
is compared to the existing rationalization by its tensor-Hom equivalence.
Finite coefficient naturality passes to the limit and then across the sheaf
adjunction to prove the actual ringed structure square. Completed identity
coherence follows by cancellation of the normalized completion unit and the
ordinary identity comparison.
Existing signatures, visibility, public imports and data definitions are unchanged.

## Proved and sorry left

Closed 28 of 45 original holes; added zero holes; split off zero statements.
These proofs use existing companion declarations, including declarations still
postponed, as intended by stage 3. No claim of absence of transitive sorry dependencies
is made. Names below are in namespace `AlgebraicGeometry.Scheme`.

Closed declarations:

- `pbcAmbientScalarComp_naturality`
- `pbcAmbientScalarShift_exists`
- `pbcCoherentScalarExtension`
- `pbcConditionalIntegral_linear`
- `pbcEmbeddingIntegerMap_quotient_kernel`
- `pbcIntegralScalarShift_exists`
- `pbcRationalScalarComp_naturality`
- `pbcRationalScalarExact`
- `pbcRationalScalarHom_laws`
- `pbcRationalScalarShift_exists`
- `pbcRationalScalarUnit_naturality`
- `pbcScalarCoefficientMap_comp`
- `pbcScalarCoefficientMap_exists`
- `pbcScalarCoefficientMap_id`
- `pbcScalarCoefficientStructureSquare`
- `pbcScalarCompletedExchange_rational`
- `pbcScalarCompletedPull_identity`
- `pbcScalarCompletedPull_rational`
- `pbcScalarCompletion_coefficients`
- `pbcScalarDirectImage_rational`
- `pbcScalarLocalization_naturality`
- `pbcScalarRationalIsTriangulated`
- `pbcScalarRationalShiftAdditive`
- `pbcScalarRationalZero`
- `pbcScalarRestrictId_exists`
- `pbcStageExact`
- `pbcSubfieldInclusion_comp`
- `pbcSubfieldInclusion_id`

Remaining original holes, all with node `prop-weil-pbc-scalar-extension` and
their retained source and complete proof docstrings:

- `pbcActualOperations_linear`
- `pbcEmbeddingAmbientTensor_preserves`
- `pbcRationalScalarHom_exists`
- `pbcScalarCompletedExchange`
- `pbcScalarCompletedPull_coefficients`
- `pbcScalarCompletedPull_comp`
- `pbcScalarCompletionIso_exists`
- `pbcScalarDirectImageMap_isIso`
- `pbcScalarDirectImage_coefficients`
- `pbcScalarDirectImage_comp`
- `pbcScalarOperations_identity`
- `pbcScalarOperations_shift`
- `pbcScalarOrdinaryPull_coefficients`
- `pbcScalarOrdinaryPull_comp`
- `pbcScalarPreservesComplete`
- `pbcStageAssociatorShift`
- `pbcStageAssociator_laws`

## No longer needed

Removed 36 of the 37 original proof-only imports of the original module. The ambient shift proof uses the upstream
`WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift` privately.
Ambient exactness uses the saturated quasi-isomorphism, resolving-class essential
constancy and distinguished-source-triangle declarations. Rational localization
uses `WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom`.
The finite coefficient naturality proof retains
`Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`. Five new proof-only
imports supplement that retained import. Removed modules:

- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Sheaf.CategoryTheory.ScalarLocalization`
- `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`
- `Mathlib.LinearAlgebra.TensorProduct.Basic`
- `Mathlib.RingTheory.Localization.Away.Basic`
- `Sheaf.Paper.CompletedTowerDirectImage`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`
- `Sheaf.Paper.ExtendedCechCompletionModel`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Mathlib.CategoryTheory.Sites.Limits`
- `Sheaf.CategoryTheory.RingedKoszulCompletionReflector`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.CompletedDirectImageLimits`
- `Sheaf.Paper.CondensedAmbientExchange`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.Paper.PerfectProjectionFormula`
- `Sheaf.Paper.RingedPushforwardCompletion`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.WeilCompletedTensorReflector`

In the current source snapshot, these removals also remove 14 project modules
from the `TargetsCheck` import closure (checked by traversing project source imports):

- `Sheaf.CategoryTheory.IndexedCoveringClass`
- `Sheaf.CategoryTheory.RingedPresentationTransport`
- `Sheaf.CategoryTheory.RingedToposEquivalenceRingTransport`
- `Sheaf.CategoryTheory.RingedToposRingSquare`
- `Sheaf.CategoryTheory.RingedToposSitePresentation`
- `Sheaf.CategoryTheory.RingedToposSquareTransport`
- `Sheaf.CategoryTheory.SheafSubcategoryComparison`
- `Sheaf.CategoryTheory.SiteOfSheafGenerators`
- `Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization`
- `Sheaf.CategoryTheory.SmallSetOfCoveringFamilies`
- `Sheaf.CategoryTheory.ToposCompatibleGenerators`
- `Sheaf.CategoryTheory.ToposSitePresentation`
- `Sheaf.Paper.RingedPushforwardCompletion`
- `Sheaf.Paper.RingedStrictTowerProjectionMorphism`

Unresolved companion proofs retain their original documented mathematical plans and
DAG proof dependencies, and may need some of this theory when proved. The blueprint
unit route is unchanged. The additional proof dependencies are the existing nodes
`lem-pur-right-kan-extension-coherent-shift`,
`lem-pur-quasi-isos-saturated-triangulated`,
`lem-pur-resolving-class-essential-constancy`, and
`lem-pur-left-derived-kan-source-triangles`; no new node was introduced.

## Where the brief, the DAG or earlier work was wrong

The retained earlier report undercounted the closed holes. The current source
comparison confirms 45 original holes, 28 closed and 17 remaining, zero added.
The coefficient-limit proof needed explicit sheaf endpoints and a sectionwise
presheaf equality mapped through sheafification; ordinary rewriting exposed large
objects and caused expensive recovery elaboration. No statement is disputed.

The interface scanner reports seven declaration-local commands
`attribute [-instance] ULift.module in` as a top-level command change. No public
signature, data definition, visibility, public import or global option changes.
The change record `coord/changes/P9-pbc-scalar-local-proof-context.md` documents
the exact commands and the recorded transitive consumers. No consumer needs
adaptation. The absence of this record caused the retained preflight rejection;
the record is now included for independent review.

Earlier attempts compiled the retained module cleanly, including the 21-proof
version in 23.9 seconds (`scratchpad/current-compile.log`). Several resumed calls
received no answer from the compile server. In the current resumption, the first
required dry run likewise returned no answer within 200 seconds. Its retry reached
preflight and rejected only the absent change record above. Neither call pushed.
Fresh validation: the current 28-proof module compiles without warnings in
45.9 seconds (`scratchpad/continuation33-compile.log`). The preceding dry run
refused two retired Sheaf imports; both now use their current WeilConjectures
modules. Nothing has been pushed. The dispatcher refreshed `.budget.start` on
resumption (observed 2026-10-19 17:06 UTC); the retained work predates that clock.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
