## What changed

The assigned theorem is reduced to the normalized tensor comparison for restriction
along a coefficient-ring isomorphism. Its signature is unchanged. The proof constructs
the source and target isomorphisms, derives the counit identity from the existing
coefficient-change adjunction theorem, and transposes the tensor/counit composites.
A final naturality equation handles the arbitrary isomorphism Q ≅ P.

The new module Sheaf.Paper.ProEtaleCoefficientTensorTransport constructs the canonical
identity-restriction and pullback comparisons as explicit composites of existing
natural isomorphisms. The assigned module privately constructs the matching
direct-image comparison and proves the normalized adjunction equation. The remaining
theorem concerns only tensor and inverse image. It has no direct-image functor, projection mate, perfectness hypothesis or
isomorphism-locus assertion.

Proof imports add that module and RingedDerivedTensorNative. A private explicit
construction packages its monoidal tensor and flat K-flat representative isomorphism
as the required ordinary tensor model. All existing public imports and
existing declaration signatures remain unchanged. No other existing module is edited.

Validation: lcompile.py --all compiled the final tensor-comparison module in 3.0
seconds and the assigned module in 20.6 seconds, without errors or warnings. The
original theorem signature was compared verbatim with the repository source.

## Proved and sorry left

Closed the one textual hole in
AlgebraicGeometry.Scheme.completedTensorProjectionCoefficientTransport, node
lem-pbc-completed-tensor-projection-coefficient-transport, by a complete Lean proof
from the tensor comparison and the existing derived adjunction comparison.

Added one hole:
AlgebraicGeometry.Scheme.CoefficientTensorTransport.tensorComparison, node
lem-pbc-coefficient-restriction-tensor-comparison. Its whole proof is `by sorry`.
Its docstring gives the flat K-flat representative construction and the pure-tensor
proof of the compatibility square.

This is a decomposition: one upper hole closed, one strictly smaller tensor-coherence
hole added, net zero holes closed. The categorical mate algebra, normalization of the
adjunction comparison and coefficient-object naturality are proved, with no additional
holes. No definition contains a hole or chooses data from an unproved existence claim.

## No longer needed

No existing import or dependency module is pruned. The attempted proof import of
OrdinaryScalarTensorBalancing was removed when the delivery gate found that module
unavailable in its source; the explicit native-model construction replaces it. The original K-flat resolution
and tensor-descent dependencies remain needed by the new tensor-comparison node;
they have not been declared obsolete merely because the main proof now imports the
comparison as a separate theorem. The source library is untouched.

## Where the brief, the DAG or earlier work was wrong

The original proof plan compressed the restriction/tensor comparison and its
compatibility with the two canonically normalized pullback tensor comparisons into
one prose step. The existing coefficient-change adjunction theorem supplies the
adjunction comparison, but does not state that tensor square. The delivery isolates
that precise missing step and supplies the categorical argument from it. No false
statement or change of the unit route was found.

The new tensor step applies to arbitrary input objects and ring-sheaf isomorphisms.
It needs no invertibility of a projection arrow. The argument also applies to zero
objects, zero rings and empty sites, since restriction along a ring isomorphism is
an exact equivalence and all maps are defined on the same pure tensors.

## New nodes

lem-pbc-coefficient-restriction-tensor-comparison records the natural restriction/tensor
isomorphism and its compatibility with geometric tensor pullback for fixed tensor
models. This is the tensor-only portion of original proof steps 1 and 3. The main
proof separately constructs the direct-image and projection-arrow square and then
transports the coefficient object. The node records the source, three kinds of
Mathlib search, and the full representative proof plan. There are no change records,
because no existing statement, definition, visibility or public import changes.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
