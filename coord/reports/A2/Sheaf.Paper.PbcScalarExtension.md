## What changed

Restored the assigned module from its rework quarantine and replaced 29 of its 45 original
sorry bodies with Lean proofs. Public declaration signatures are preserved. The completed
scalar/pullback comparison is expressed directly by its two canonical components to
avoid expensive unfolding of identity and associator isomorphisms. No source-library
module, target statement, or other consumer is edited. The change record is
`coord/changes/a2-pbc-completed-scalar-comparison.md`.

The proofs construct the residue-compatible coefficient limit maps, prove their identity
and composition equations, and establish the rational tensor functor laws and naturality.
Canonical shifts descend by Kan-extension uniqueness, full-subcategory faithfulness, and
scalar localization. The existing counit-normalized derived-tensor theorem supplies
ambient exactness; integral inclusion and localization then supply rational exactness.
The main coherent-package theorem assembles its existing named companion statements.

Completion coefficient coherence follows by cancelling the reflector unit. Preservation
of completeness follows from the unit-normalized scalar/completion comparison. Completed
identity and coefficient-composition coherence reduce to ordinary coherence and completion
normalization. The conditional direct-image and pullback comparisons descend on tensor
Hom generators, with uniqueness fixed by their stated components.

Only three private proof imports remain: RationalizationHom,
RightKanExtensionCoherentShift, and DerivedScalarExtensionCounitShift. Added private helpers
are fully proved. Reordered completeness preservation and completion coefficient coherence
after the statements used in their proofs. Instance disabling for the tensor-action diamond
is scoped to proofs. A proved identity-unit normalization lemma allows the existing
identity comparison definitions to be locally irreducible during the coherence proof.
Rational Hom maps are also locally irreducible during tensor calculations, and the
normalized transition functor is locally irreducible during package assembly; their APIs
supply the equations without repeated unfolding of chosen witnesses.
The node records the two existing general lemmas used for the canonical
shift and exactness argument and keeps every dependency needed by the remaining proof plans.

Validation: lcompile.py compiled the final file cleanly in 40.1 seconds. After an earlier
delivery compile timed out, local opacity for the selected Hom maps and transition
functor reduced elaboration cost. The delivery runs its independent compile and preflight
checks. No local Lean or Lake invocation was used.

## Proved and sorry left

Closed 29 original holes; added zero holes; split off zero statements. These are proofs
from the existing library declarations, some of which retain their own named proof holes.
This is not an axiom-free completion of the entire scalar-extension package.

Closed declarations (all in AlgebraicGeometry.Scheme):

- `pbcScalarRationalZero`
- `pbcScalarRationalShiftAdditive`
- `pbcScalarRationalIsTriangulated`
- `pbcEmbeddingIntegerMap_quotient_kernel`
- `pbcScalarCoefficientMap_exists`
- `pbcRationalScalarHom_laws`
- `pbcScalarCoefficientMap_comp`
- `pbcAmbientScalarComp_naturality`
- `pbcRationalScalarComp_naturality`
- `pbcScalarRestrictId_exists`
- `pbcScalarCoefficientMap_id`
- `pbcRationalScalarUnit_naturality`
- `pbcAmbientScalarShift_exists`
- `pbcIntegralScalarShift_exists`
- `pbcScalarLocalization_naturality`
- `pbcRationalScalarShift_exists`
- `pbcRationalScalarExact`
- `pbcSubfieldInclusion_id`
- `pbcSubfieldInclusion_comp`
- `pbcStageExact`
- `pbcScalarPreservesComplete`
- `pbcScalarCompletedExchange_rational`
- `pbcScalarCompletedPull_identity`
- `pbcScalarCompletedPull_coefficients`
- `pbcScalarCompletion_coefficients`
- `pbcConditionalIntegral_linear`
- `pbcScalarDirectImage_rational`
- `pbcScalarCompletedPull_rational`
- `pbcCoherentScalarExtension`

The 16 original holes left, all attached to `prop-weil-pbc-scalar-extension`, are:

- `pbcEmbeddingAmbientTensor_preserves`
- `pbcRationalScalarHom_exists`
- `pbcStageAssociator_laws`
- `pbcStageAssociatorShift`
- `pbcScalarCoefficientStructureSquare`
- `pbcScalarDirectImageMap_isIso`
- `pbcScalarCompletionIso_exists`
- `pbcScalarCompletedExchange`
- `pbcScalarOperations_shift`
- `pbcScalarOperations_identity`
- `pbcScalarDirectImage_comp`
- `pbcScalarOrdinaryPull_comp`
- `pbcScalarCompletedPull_comp`
- `pbcScalarDirectImage_coefficients`
- `pbcScalarOrdinaryPull_coefficients`
- `pbcActualOperations_linear`

Each remaining hole is its original named public theorem, with its source and proof in
words retained. No partial proof or private helper contains a sorry.

## No longer needed

Removed these private imports, which supplied no declaration used by the implemented
proofs or the module's public interfaces:

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
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
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

No DAG node or library module is withdrawn. In particular, the finite-free,
stratified-perfect, projection-formula, and geometric coherence nodes remain needed by the
16 untouched companion statements and their documented proof plans. Removing their unused
private imports from this partially proved module does not withdraw those dependencies.
The quarantined source and its Lean attachment are preserved.

## Where the brief, the DAG or earlier work was wrong

The live item path was absent because it was quarantined, as recorded in coord/rework.tsv.
Restored the archived module rather than treating that absence as a withdrawal.

No mathematical statement was weakened or disputed. The original three triangulation
adapter holes can be filled by projections from the identical existing witness. The
published canonical tensor counit permits a shorter shift/exactness argument through
existing general Kan and derived-tensor results. The completion comparison also makes
preservation of completeness a formal consequence, avoiding a second finite-basis proof.

The inherited ULift scalar-action instance competes with the localization action when
elaborating raw tensor Hom formulas. Proof-local instance scopes select the intended
localization action without changing any public construction.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
