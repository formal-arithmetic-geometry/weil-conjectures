## What changed

Proved `AlgebraicGeometry.ProEtale.FiniteStrataCompletion.finite_strata_completion_detection`
with its original statement and definitions. Added private proved helpers for conversion
of the finite indexed refinement to the recursive tree, module and homology detection,
scalar presentation transport, and completeness via the cone of the specified augmentation.
The scalar proof uses a private, constructed leaf-to-cover projection with a proved
composition equation. This avoids expensive conversion of whole pullback-cover
constructions inside the scalar-module isomorphisms, while preserving all definitions.
Used the existing `StrictCompletionRestrictionComparison` rather than reconstructing
its normalized principal-cone/Roos comparison. Updated the owning DAG proof accordingly.
No source-library file, public signature, or public import was changed.
Retained the two unit-route imports `WeaklyEtaleStability` and `CartesianCoefficients`.
Local proof-elaboration attributes are recorded in
`coord/changes/Y6-finite-strata-proof-elaboration.md`; they do not alter public data.
Validation: the complete item compiled cleanly through `lcompile.py` in 33.0 seconds,
with no warnings or errors. The theorem signature and all five original definitions
were checked unchanged; every line is at most 100 characters.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.FiniteStrataCompletion.finite_strata_completion_detection`
(node `lem-sfb-finite-strata-completion-detection`). The item has zero remaining holes.
Added zero holes and zero new public statements. The proof uses the adopted, proved
unbounded K-flat resolution theorem and existing stated results, including the still-unproved
`StrictCompletionRestriction.strict_completion_restriction_comparison`, as permitted
by stage 3. Its object data are only unpacked inside proofs.

## No longer needed

Removed these direct proof imports:

- `Mathlib.AlgebraicGeometry.Sites.Fpqc`
- `Mathlib.AlgebraicGeometry.Sites.Proetale`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.Paper.PrincipalReductionConeCalculus`
- `Sheaf.Algebra.Homology.RoosConeCalculus`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus`
- `Mathlib.CategoryTheory.Sites.LocalProperties`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
- `Mathlib.CategoryTheory.Adjunction.CompositionIso`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Sheaf.CategoryTheory.FiniteColimitMatrixCokernels`

The following original proof dependencies are not used directly by this proof:

- `lem-weil-pbc-fpqc-covering-axioms`
- `lem-weil-pbc-proetale-immersion-limit-preservation`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-pe-principal-reduction-cone-calculus`
- `lem-pe-roos-cone-calculus`
- `lem-pe-completion-triangle-comparison`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `lem-sfb-exact-open-closed-unbounded-calculus`
- `lem-pur-quasi-iso-cone-acyclic`
- `def-sfb-module-upper-star-comp`
- `lem-weil-pbc-immersion-base-change-lft`
- `lem-sfb-finite-colimit-matrix-cokernels`

Product preservation, principal-cone/Roos comparison, and normalized completion-unit
transport are supplied by the existing strict restriction comparison, so their lower
nodes remain needed by that declaration. They are not claimed as globally withdrawn.
The unbounded open/closed calculus is unnecessary here: apply the proved module
zero criterion to each homology object instead. The general finite-colimit matrix
lemma is replaced by the existing scalar free/matrix and cokernel comparisons.
The argument for original strata uses finite quasi-compact joint detection directly;
it does not need to compare each leaf-cover member back to an original-cover member
by proving that its factor map is an immersion. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically sound, but its completion-comparison subargument already
has the declared module `Sheaf.Paper.StrictCompletionRestrictionComparison`. Reusing
its actual unit equation avoids duplicating that result or adding a new hole.
The indexed refinement theorem requires a genuine conversion to the recursive
`SchemeRefinementTree`, including transport of the root isomorphism; the proof
supplies that conversion by strong induction. Empty schemes and rank-zero scalar
presentations are handled by the same constructions.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
