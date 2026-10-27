## What changed

Proved `AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_iff_topologicalKrullDimAt_fiber_eq_zero`
in `Sheaf.AlgebraicGeometry.LocallyQuasiFiniteRelativeDimension`, preserving its exact signature
and all public imports. The proof follows Stacks 0397's second proof and Properties 0H7C.
A local `hpoint` equivalence uses the existing proved forward isolation theorem and the
proved isolated-fibre-point affine-pair theorem. In the dimension-zero converse, an affine
Noetherian neighbourhood reduces the argument to the existing zero-dimensional Noetherian
T0 finiteness theorem. A finite T1 neighbourhood is discrete, and its singleton maps to an
open singleton in the fibre.

Added private proof imports of
`WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated`,
`WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs`, and
`Mathlib.AlgebraicGeometry.Noetherian`. Updated the existing node's proof, proof dependencies,
and proof origin to this argument, and removed its obsolete ring-equivalence tool approval.
No declaration, definition, target, source-library module, or unit route changes.

The final single-file server compile passed without errors or warnings (4.1 seconds).
The proof does not assume nonempty source, quasi-compactness, or global Noetherianity of a
fibre: all choices occur after fixing a source point, and Noetherianity is used only on an
affine neighbourhood. Thus the empty-source and non-quasi-compact cases remain covered.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_iff_topologicalKrullDimAt_fiber_eq_zero`
(node `lem-trf-locally-quasi-finite-relative-dimension-zero`).

Zero holes remain in the item; zero holes added; zero statements split off.
The delivery checks also probe the axioms of the completed declaration.

## No longer needed

Removed private proof imports:

- `Sheaf.RingTheory.QuasiFiniteAtPrimeZeroFibreDimension`.
- `WeilConjectures.RingTheory.QuasiFiniteAtPrime` (already publicly available through
  the unchanged quasi-finite definitions import).

The updated proof does not directly require these former DAG dependencies:

- `lem-weil-pbc-affine-open-spec-points`.
- `def-weil-affine-spectrum`.
- `lem-weil-pbc-lft-affine-pairs`.
- `lem-weil-pbc-affine-open-stalk-localization`.
- `lem-weil-pbc-fibre-product-affine-spectra`.
- `lem-weil-pbc-fibre-ring-primes-bijection`.
- `def-weil-pbc-ring-map-quasi-finite-at-prime`.
- `lem-weil-pbc-ring-quasifinite-zero-fibre-dimension`.

The affine fibre comparison has been replaced by direct topology on a Noetherian open
neighbourhood of the scheme-theoretic fibre. The ring-equivalence node and its
`Sheaf.RingTheory.QuasiFiniteAtPrimeZeroFibreDimension` module are unnecessary for this
item's route. Some other listed nodes remain transitively used by the unchanged source
quasi-finiteness predicates or their existing proved isolation lemmas; this delivery
claims no global withdrawal of those declarations or modules. No Lean file is withdrawn.
The obsolete top-level `tool_uses` entry
`lem-weil-pbc-ring-quasifinite-zero-fibre-dimension` is removed.

## Where the brief, the DAG or earlier work was wrong

The original affine tensor-product comparison plan is longer than necessary. Stacks 0397
already gives the locally Noetherian second proof, which Mathlib's finite-type base change
and local Noetherianity API supports directly. The unchanged theorem docstring describes
the earlier valid affine route; the updated DAG and this report describe the implemented
second proof. No mathematical statement was false or repaired.

The replacement route uses the existing proved generic tool
`lem-sc-zero-dim-noetherian-closed-finite` from the curve-estimates chapter, attached to
`IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero`. It is a theorem of
Noetherian T0 topological spaces, not a replacement of any unit step. Its Lean proof is
complete. The node `pqf-lem-locnoeth-lft` is an exact Mathlib leaf. No new tool approval was
written by this worker, and no new node was necessary.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
