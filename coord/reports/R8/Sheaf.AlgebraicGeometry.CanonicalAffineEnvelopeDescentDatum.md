## What changed

Proved all seven theorems in `Sheaf.AlgebraicGeometry.CanonicalAffineEnvelopeDescentDatum`.
The public signatures, definition data, docstrings and public imports are unchanged.
Private proved helpers identify the tensor spectrum, extend morphisms uniquely across a
section isomorphism, and construct the envelope transport and its cocycle. The datum is
constructed from the original universal transport, rather than chosen from mere existence.
The explicit alpha-conjugation formula follows from equivariance and affine-target uniqueness.
Updated the existing node's proof route to match these universal-point calculations.

Validation: single-file compilation through lcompile.py; final delivery preflight checks all
declaration axioms. The proof uses Mathlib's flat global-sections comparison and the proved
`Sheaf.AlgebraicGeometry.QuasiAffineBaseChange` theorem. Edge cases require no nonempty
hypotheses; in particular empty schemes and the identity envelope are included.

## Proved and sorry left

Closed 7 of 7 original holes, all in `AlgebraicGeometry.CanonicalAffineEnvelope`:
`baseChange`, `comparison_apply`, `alpha_properties`, `spectrumComparison_eq`,
`comparison_naturality`, `comparison_successive`, and `exists_descentDatum`.
All belong to node `lem-trf-canonical-affine-envelope-descent-datum`.
No sorry remains; no holes added or split off. All private helpers are proved.

## No longer needed

None. All planned mathematical dependencies remain in the proof route. The proof uses
`Sheaf.AlgebraicGeometry.QuasiAffineBaseChange` for both successive base change and the
universal double pullback in the cocycle argument. No modules or declarations are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The DAG's coordinate cocycle argument admits a shorter Lean
implementation in transport form: extend the universal transport by its section map and
check identity/cocycle by uniqueness on the universal single/double base changes. This
proves the same datum, all-point equivariance, and alpha-conjugation formula. The proved
base-change theorem supplies the relative quasi-affine instances used here.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
