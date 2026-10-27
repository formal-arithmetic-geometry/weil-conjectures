## What changed

`Sheaf.Paper.CompletedOpenTensorSystemRealization` proves the completed realization,
completion-unit equation and uniqueness, and the restriction identity from compatible
strict representatives. The proof uses the actual reduction/total-limit adjunction.
It proves normalization by identifying the open system with a reduction, constructs the
completed isomorphism by the stated source and target identifications, and calculates its
unit equation with the actual counit. A private Hom-injectivity lemma proves uniqueness
and the restriction identity.

`Sheaf.Paper.CompletedOpenTensorRepresentatives` contains the 21 original helper
declarations verbatim and a separate compatible-representative construction theorem.
The original module retains its original public imports and publicly reexports this
module. No target, existing signature, definition body or public visibility changes.
The change record is `coord/changes/U8-completed-open-tensor-representatives.md`.
Both delivered modules compile cleanly with the prescribed compiler. Both unchanged
downstream importers also compile against the relocated interface:
`CompactSupportScalarProjectionIdentification` and `ConcreteProjectionFieldDescent`.
The latter set check reported 67.3 seconds under current load; its source was unchanged.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.CompletedOpenTensor.completedOpenTensorSystemRealization`.
The original item had one hole and now has zero. This is not an axiom-free closure because the retained construction remains a dependency.

Added one hole:
`WeilConjectures.CompletedOpenTensor.completedOpenTensorRepresentatives`, node
`lem-pur-completed-open-tensor-representatives`. It is the compatible-model and strict
representative construction, before any assertion about completed comparisons. Its
source, full construction argument and edge cases are in the docstring and node.

This is a decomposition: 1 original hole closed, 1 separate hole added, net 0 holes.
The private generic adjunction squares, completeness transport, normalized-system transport,
completion Hom-injectivity,
realized extension unit, realized tensor unit, restricted tensor unit and completed-context
argument are proved without local holes. The item still transitively depends on the
retained construction and the declared reconstruction results.

## No longer needed

Removed proof-only imports from the item:
`Sheaf.Paper.WeilCompletedTensorReflector`,
`Sheaf.Paper.ConstantCompletionEquivalence`,
`Sheaf.SixFunctors.OpenQuotientKoszulCompleteness`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, and
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
The reconstruction-adjunction import is retained because the proof uses it.

The completed-comparison argument does not need a separate reflector construction,
tensor-substitution preservation of normalization, finite-evaluation faithfulness, or
completeness of either original tensor input. It gets normalization directly from q_U
and reduction_normalized, and gets uniqueness directly from reconstruction and the
triangle identities. These portions of the original nine-step plan are replaced by the
explicit adjunction calculation in the updated node.

No module is withdrawn or claimed globally unnecessary. The unit route through
`sk-prop-sf-pf-reduction` is preserved: this is still the extension-by-zero
comparison used for the compact-support tensor argument. The representative construction
still needs the original strict-model, K-flat, quotient/Koszul and ordinary open tensor
mathematics; all original public imports remain to preserve the existing interface.
Thus no globally pruned module is reported.

## Where the brief, the DAG or earlier work was wrong

The existing existential comparison declarations choose their calculi and open operations
independently; they cannot simply be destructured to fill one Context with the required
literal tensor equalities, actual-unit completion comparisons, and sameOpen equation.
The retained construction states precisely that compatibility task, using one canonical
set of models. No existing statement was marked false or weakened.

The original normalization step required completeness of the input factors unnecessarily
for this conclusion: q_U already identifies the system with a normalized reduction.
The source-unit/counit calculation proves the completed conclusions directly and also
handles incomplete ordinary tensor objects. Identity and empty opens, zero complexes,
unbounded complexes and independent site/coefficient universes remain admitted.

## New nodes

`lem-pur-completed-open-tensor-representatives` is the compatible strict construction in
original proof steps 1--3, together with the shared Context presentations those steps
require. It does not restate the completed realization theorem: the entire completed
isomorphism, its unit equation, uniqueness and restriction conclusions are proved in
the parent from it. The node owns the verbatim relocated helper declarations and the
one retained construction theorem. Change record:
`coord/changes/U8-completed-open-tensor-representatives.md`.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
