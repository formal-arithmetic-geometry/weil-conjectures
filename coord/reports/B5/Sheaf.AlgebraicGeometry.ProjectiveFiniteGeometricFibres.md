## What changed

Proved `AlgebraicGeometry.isFinite_of_isProjective_of_finite_geometricFibres` in
`Sheaf.AlgebraicGeometry.ProjectiveFiniteGeometricFibres`, preserving its complete signature.
Projectivity supplies properness. The geometric point has singleton image because its
spectrum is nonempty and the residue-field morphism is constant. Mathlib's
`Scheme.Pullback.range_fst` identifies the image of the finite geometric fibre with the
ordinary set-theoretic fibre. The existing source-library proper-with-finite-fibres
criterion then proves finiteness.

Updated the declaration's proof explanation and the existing node's proof, proof dependencies,
proof origin, and obsolete tool approvals to match this route. The unit has no proof steps
or realized nodes, and its statement and route remain unchanged. No signatures or definitions
were changed, and no new module or node was added.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.isFinite_of_isProjective_of_finite_geometricFibres`
(node `lem-fin-projective-finite-fibres`).

Holes closed: 1 of 1. Holes added: 0. Split-offs: 0. No `sorry` remains in the delivery.
The proof uses the existing proved properness instance and the source library's proved
`IsFinite.iff_isProper_and_finite_preimage_singleton`, together with Mathlib's range lemma.

Edge cases: the spectrum of the algebraic closure is nonempty, including in arbitrary
characteristic; the geometric fibre itself may be empty. Finiteness of its image handles
that case without a nonemptiness assumption on the fibre. The target may also be empty,
in which case the assertion about all its points is vacuous.

## No longer needed

Removed proof imports:

- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: redundant via the public projectivity
  import; its properness theorem is still used through the projectivity instance.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`.
- `Sheaf.AlgebraicGeometry.FiniteIffProperFiniteFibres`: retired re-export; import the
  already-present source module `WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite`
  directly for the criterion.

The proof no longer needs these node dependencies:

- `lem-weil-pbc-field-extension-base-change-faithfully-flat`.
- `lem-weil-pbc-faithfully-flat-surjective-spectrum`.
- `lem-weil-pbc-surjective-base-change`.
- `def-pc-scheme-fibre`: no separate ordinary scheme fibre or fibre homeomorphism is needed.
- `pqf-def-locnoeth` as a proof dependency: the stronger existing criterion does not require
  the Noetherian hypotheses. It remains a statement dependency because the signature is
  unchanged.

The first three obsolete top-level tool approvals were removed, preserving the approved
proper-with-finite-fibres criterion. The new proof instead uses the existing Mathlib leaf
`lem-weil-pbc-base-change-image`, whose chosen-pullback range clause is precisely
`Scheme.Pullback.range_fst`. No claim is made that nodes used by other parents are globally
unreachable.

## Where the brief, the DAG or earlier work was wrong

The planned faithful-flatness and iterated-pullback comparison was unnecessary. The already
available pullback range formula compares the geometric fibre directly to the set-theoretic
fibre. The finite/proper criterion is already proved in the source library and does not
require the target to be locally Noetherian or quasi-compact; the original hypotheses have
been retained verbatim. No false statement or definition repair was needed.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
