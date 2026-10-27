## What changed

The signature of `AlgebraicGeometry.ProEtale.supported_image_torsion_reductions_cohomology_vanishes`
is unchanged. Its proof now assembles the existing finite coefficient theorem and a
proved induction from the first integral coefficient reduction to every positive power.
The already proved `supported_finite_image_cohomology_vanishes` and the private
affine-limit torsion-dimension argument are unchanged.

The new private helper `integral_reduction_cohomology_of_first` applies to any
integral derived complex and any fixed integer cohomology degree. It obtains the
canonical tensor/extension-restriction comparison from
`PrincipalNormalization.principal_tensor_scalar_extension`, and the distinguished
coefficient triangles from `DerivedNakayama.derived_nakayama_resolution`. After
applying derived sections followed by degree-q homology, the triangles give exact
three-term sequences. Induction, with zero outer terms, proves vanishing at every
positive coefficient power. This uses no completeness, flatness, classicality or
image/reduction interchange.

`Sheaf.Paper.SupportedImageFirstReductionCd` contains the single remaining first-power
geometric estimate. Its statement is precisely the parent's integral case at index
zero (modulo pi), retaining all the hypotheses and edge cases. It is strictly a case
of the old statement: finite coefficients and all higher coefficient powers are
handled by real Lean code in the parent. Its inherited dispute is explicit; no use
is made of the refuted unrestricted local comparison lemma.

The parent has private proof imports of the new module,
`Sheaf.Paper.PrincipalTensorScalarExtension`, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`.
Existing public imports are preserved as the existing reexport interface. The new
module's imports omit finite-discrete encoding, admissible coefficient classes,
coefficient-extension finiteness and the unused derived pushpull wrapper.
The parent DAG proof and proof dependencies now match the coefficient-power induction.
No definition, existing public signature, source-library declaration or target changed.

The first compile of both modules passed: new module 43.6 seconds; parent 49.0 seconds.
The final sources are checked again by lcompile and by deliver3's compile/probe preflight.

## Proved and sorry left

Closed the direct hole in
`AlgebraicGeometry.ProEtale.supported_image_torsion_reductions_cohomology_vanishes`
(node `lem-sfb-supported-image-torsion-reductions-cd`).
The finite conjunct is assembled from the existing stronger finite-image theorem.
The higher-power integral induction is proved by the new private helper
`integral_reduction_cohomology_of_first`.

Added one direct hole:
`AlgebraicGeometry.ProEtale.supported_image_first_reduction_cohomology_vanishes`
(node `lem-sfb-supported-image-first-reduction-cd`, new module
`Sheaf.Paper.SupportedImageFirstReductionCd`). No direct sorry remains in the item
module; exactly one remains in the delivery. Holes closed 1, holes added 1, net 0:
this is a decomposition, not a completed geometric vanishing proof.

Existing imported obligations are used as intended by stage 3. In particular
`PrincipalNormalization.principal_tensor_scalar_extension` remains sorry in its
own unmodified module; this delivery does not claim to prove it. The unchanged
finite-image theorem also uses its existing classical-origin and evaluation
comparison obligations.

## No longer needed

No existing Lean import or module is withdrawn. The new module was trimmed of
unused public imports of `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
`Sheaf.Paper.CondensedModuleDerivedPushpull`,
`Sheaf.Paper.LocalizingAdmissibleCoefficients`, and
`Sheaf.Paper.FiniteDiscreteOrdinaryEncoding` before delivery.

The parent's direct integral proof no longer invokes
`lem-sfb-supported-image-koszul-comparison-nonpositive` or
`thm-sp-truncation-e2`. It no longer directly uses
`lem-pe-principal-reduction-cone-calculus`,
`lem-sfb-internal-module-operations-transport`,
`lem-sfb-ringed-site-unbounded-leray-sections`, or
`lem-weil-l-adic-extension-integers-dvr`. The obsolete corresponding top-level
parent tool_uses entries were removed, retaining the others in their original order.
These nodes/modules are not claimed globally pruned: the new first-power node
retains the cone/scalar-forgetting part of the attempted geometric argument as
an unresolved plan. The affine-limit torsion theorem and proAffineEtale definition
remain used by the unchanged finite coefficient proof in this same module.

The parent now uses only the finite-image node, the new first-power node, the
coefficient resolution node, the tensor/scalar-extension comparison node, and the
proved generic triangulated-right-derived-functor node. No chapter or unit route
is bypassed: this is the algebraic coefficient-power step below the same
compactification-coherence descendant obligation.

## Where the brief, the DAG or earlier work was wrong

The source and Q09 report were read. HRS condition (8.1) is a heart-cohomology
hypothesis; Lemma 8.6 supplies particular geometric cases. Neither gives the old
unrestricted local relative nonpositivity claim. Q09's explicit counterexample
makes that claim false and the corrected local theorem requires Noetherian S,
which the parent does not assume. The old parent proof steps therefore cannot
establish even the first-power global estimate. That mathematical gap remains
visible in both Lean and the new node, with exact generality WANTED.

STATEMENT-DISPUTED: the remaining first-power global assertion requires re-review;
no counterexample to that global assertion is claimed. No geometric hypothesis was
silently inserted and no weaker parent statement was substituted. The new node
must not be read as a reference-backed proof of the unresolved geometric step.

The actual improvement is the checked algebraic assembly: only the first power
needs new geometric input. Empty schemes, empty paths, zero maps/images, d=0 and
E=Q_ell retain the original meaning. The induction includes n=0 as its base and
n+1 as its step, with the library index n corresponding to pi^(n+1).

The local unit record carries an older smooth-purity wording while the latest
blueprint has the six-functor coherence wording. Neither record was edited; this
delivery stays below the assigned descendant estimate.

## New nodes

`lem-sfb-supported-image-first-reduction-cd` is the first-power specialization of
the existing global integral estimate, in the same chapter and unit. Its Lean
attachment is `AlgebraicGeometry.ProEtale.supported_image_first_reduction_cohomology_vanishes`
in `Sheaf.Paper.SupportedImageFirstReductionCd`. It has source/proof-status warnings,
edge-case checks, the existing scalar-resolution and affine-limit inputs, and fresh
LeanFinder, Loogle and Mathlib grep searches. Whole-blueprint/DAG searches found no
existing first-power global supported-image cohomological bound. It is not the
Noetherian relative-comparison node, the all-power parent, or the derived Nakayama
zero-detection theorem.

No change record is needed: only proofs of existing declarations changed, and a
new theorem/module/node was added. No existing interface or definition changed.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
