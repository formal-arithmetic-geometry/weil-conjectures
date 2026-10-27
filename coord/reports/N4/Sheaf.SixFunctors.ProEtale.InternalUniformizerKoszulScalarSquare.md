## What changed

Completed the change-of-generator and power/tensor algebra in
`Sheaf.SixFunctors.ProEtale.InternalUniformizerKoszulScalarSquare`, preserving its
statement and public imports. The proof uses one new general, proved theorem
`CategoryTheory.ringed_regular_generator_association` and one remaining coefficient
realization theorem, in separate modules.

The association theorem constructs the two maps from the ring module to the ideal
module. Regularity and principality make the uniformizer map invertible. The actual
slice generating-sections hypothesis makes the other map epic. Local lifting of 1
shows that an epic rank-one scalar is invertible, including on a site whose section
rings need not be domains. The item then raises the resulting automorphism to the
required power, applies the single-complex and tensor functors, and uses the fixed
inverse right unitor.

## Proved and sorry left

Closed the item's one hole in
`AlgebraicGeometry.ProEtale.InternalCompletionTransport.uniformizer_koszul_scalar_square`.
Proved the new theorem `CategoryTheory.ringed_regular_generator_association` without
any holes in its module.

Added one hole:
`AlgebraicGeometry.ProEtale.InternalCompletionTransport.uniformizer_scalar_realization`
(node `lem-sfb-internal-uniformizer-scalar-realization`). It asserts the regular
constant uniformizer section and its action under the prescribed coefficient
transport. It has no arbitrary generator, generating-sections hypothesis, or
existential change of source basis. The entire argument passing from that section
to the supplied generator, and the construction of the basis change, are proved.

This is a decomposition: one original hole closed and one strictly smaller hole
added, hence zero net holes closed. No holes remain inside the item's proof; no
axioms or definitions with postponed data were added.

Server compilation passed without warnings for all three delivered modules: the
association theorem in 8.4 seconds, the coefficient statement in 38.6 seconds,
and the completed item in 8.0 seconds. The original item signature and public
imports were compared verbatim and are unchanged.

## No longer needed

No existing public import was removed, and no existing module is withdrawn or
claimed globally prunable. The item's direct proof now needs only the new regular
generator association and coefficient realization, together with its existing
Koszul scalar/tensor definitions. Its former direct proof dependencies
`det-prop-integral-criterion-constant-coefficients`,
`def-sfb-integral-constant-model-realization`, and
`lem-pe-internal-section-tensor-comparison` are localized to the coefficient
realization node; they remain needed there. The original section-transport,
quotient-model, principal-scalar and Koszul modules also remain needed in its
statements or in the coefficient subproblem.

The new association module's redundant proof imports
`Mathlib.Algebra.Category.Grp.EpiMono` and
`Mathlib.CategoryTheory.Sites.Abelian` were removed; both are already supplied by
its public dependency closure. It retains `Mathlib.CategoryTheory.Sites.EpiMono`
for the local lifting argument.

## Where the brief, the DAG or earlier work was wrong

No disputed statement, source-library repair, interface change, or unit-route
change. The DAG's regular-generator gluing argument is implemented categorically
using the ideal module and slice free-module presentations. The coefficient
normalization in the DAG remains a separate genuine part of the argument; the
existing discrete quotient comparison alone does not state compatibility with the
prescribed transported scalar action.

## New nodes

`lem-sfb-ringed-regular-generator-association` records the fully proved regular
principal ideal sheaf argument. Its statement includes zero rings and empty sites,
and uses only sectionwise regularity, principality and the given slice generator
interface.

`lem-sfb-internal-uniformizer-scalar-realization` records the remaining constant
coefficient normalization and regularity argument. Its docstring gives the full
construction and proof in words, with the source and dependencies. Unlike the
assigned statement it fixes the target basis to the inverse right unitor and has
no variable generator or change-of-basis problem. Both nodes inherit the assigned
unit and blueprint ancestry. No change record is required: only the item and new
modules/nodes are changed.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
