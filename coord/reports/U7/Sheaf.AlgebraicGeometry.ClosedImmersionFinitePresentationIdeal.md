## What changed

Proved `AlgebraicGeometry.IsClosedImmersion.finitePresentation_iff_isFiniteType_ker`
without changing its statement. Added two proved private helpers: identification of
finite affine ideal sections with a finitely generated ideal, and the ring criterion
for a surjection to be finitely presented. The proof uses the existing affine
finite-type criterion and quasi-coherence of closed-immersion pushforward and kernels.
Updated the assigned DAG node to describe this proof. Added private proof imports
for `Modules.QuasicoherentKernel`, `QuasicoherentPushforwardQcqs`, and Mathlib
`Morphisms.Separated`.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.IsClosedImmersion.finitePresentation_iff_isFiniteType_ker`
(node `lem-trf-closed-immersion-finite-presentation-ideal`).
No holes remain in this module. No holes added; no split-off statements.
The final remote single-file compile passed in 5.9 seconds. The new proof imports
passed the import-direction cycle checks. Delivery preflight supplies the axiom check.

## No longer needed

Removed unused private imports:
`Mathlib.AlgebraicGeometry.AffineScheme`,
`Mathlib.AlgebraicGeometry.Morphisms.Integral`,
`Mathlib.AlgebraicGeometry.Morphisms.Proper`, and
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed`.

The direct Mathlib quasi-compactness and quasi-separatedness instances avoid the
separate DAG dependencies `lem-weil-pbc-affine-scheme-qcqs`,
`lem-weil-pbc-closed-immersion-integral-separated-uc`, and
`def-weil-proper-morphism`. They are removed from this node's proof dependencies;
they are not withdrawn from the library. All other existing mathematical proof
inputs remain needed. The ring proof uses Mathlib's stronger
`Algebra.FinitePresentation.ker_fG_of_surjective`, avoiding explicit manipulation
of polynomial rings with zero variables.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The old plan was mathematically correct but did not
name the source-library kernel and pushforward results needed to establish
quasi-coherence for the actual module realization. These are now explicit in the
DAG proof dependencies. No target, public signature, definition or public import
was changed. No unit statement or unit proof step was bypassed.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
