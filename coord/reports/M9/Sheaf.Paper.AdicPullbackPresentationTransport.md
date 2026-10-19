## What changed

Proved ten original theorems in `Sheaf.Paper.AdicPullbackPresentationTransport`, with all public signatures and definitions unchanged. The coefficient proof uses the actual limit projections and constructs a natural transformation of the entire finite quotient system. Universal derived comparisons use Mathlib uniqueness. Finite transport and completion-unit transport follow by counit uniqueness, functoriality and naturality. The open inverse-mate counit formula follows from the adjunction triangle identity; equality of specified mates follows from injectivity of the mate equivalence. Added four proved private helpers. The representative counit transport helper and the existing unique evaluation normalization prove both comparison squares. Updated the existing node's proof to distinguish completed Lean arguments from the four untouched obligations, and recorded the normalized finite-evaluation construction of `lemma-weil-pbc-completed-pullback-reduction` as a proof dependency. This existing statement dependency supplies the finite comparison as a tool; no other unit's route is replaced.

Validation: remote single-file compilation passed cleanly in 21.8 seconds after import cleanup. Delivery preflight is run on this exact source. Equal quotient indices are included by naturality of the full poset diagram, and the categorical arguments require no nonempty scheme, nonzero coefficient ring or nonempty open.

## Proved and sorry left

Closed 10 of the original 14 holes, all in namespace `AlgebraicGeometry.Scheme`:

- `adic_pullback_coefficient_presentations`.
- `adicPresentationOrdinaryUniversal_proof`.
- `adicPresentationTowerUniversal_proof`.
- `adic_pullback_presentation_transport`.
- `adicPresentationEvaluationComplex_eq`.
- `adicPresentationFiniteIso_transport`.
- `adicPresentationCompletion_transport`.
- `adicPresentationComparison_squares`.
- `adicPresentationInverseMate_counit`.
- `adicPresentationInverseMate_eq`.

Added holes: zero. No decomposition and no new nodes.

Four original named theorems remain `sorry`, all attached to node `lem-cbc-adic-pullback-presentation-transport`:

- `adicPresentationConstantIso_normalized`.
- `adicPresentationEvaluationIso_exists`.
- `adicPresentationFiniteIso_transition`.
- `adicPresentationLocalizedComparison_isIso`.

The remaining normalization/evaluation obligations need descent and uniqueness on strict K-flat representatives; the finite transition obligation needs the published finite comparisons' all-quotient square; localized invertibility needs the restricted open-counit calculation. Their original statements, sources and complete proof docstrings remain intact.

## No longer needed

Removed these unused proof-only imports (including dependency imports added to the shared source during this session):

- `Sheaf.Algebra.Homology.DiagramKFlatReplacements`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`.

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.Paper.AdicCoefficientDatum`.
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`.
- `Sheaf.Paper.PbcQbarCompletedPullback`.

The completed proofs use the already constructed universal pairs rather than reconstructing K-flat replacements or resolving classes. Completion transport proves its constant square directly, independently of `adicPresentationComparison_squares`. The main unique-presentation theorem uses Mathlib `leftDerivedUnique` and `leftDerived_ext` directly. The removed direct imports' nodes may still be required by the four untouched obligations or by imported constructions; no assertion is made that their modules leave the targets' full import closure. Public imports used by the existing statement/definition interface are retained.

## Where the brief, the DAG or earlier work was wrong

No statement error or definition repair was found. The proof plan described reconstructing universal derived comparisons and checking completion transport on replacements, while the existing chosen universal pairs and natural transformations already suffice for those parts. The remaining four obligations have not been replaced by renamed statements or weaker claims.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
