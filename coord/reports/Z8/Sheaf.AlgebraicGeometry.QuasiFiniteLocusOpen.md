## What changed

Proved `AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAtPoint` in
`Sheaf.AlgebraicGeometry.QuasiFiniteLocusOpen`, preserving its complete statement,
universe, visibility, and public import. Added private, proved helpers for finite type
on an affine pair, comparison with Mathlib stalk-map quasi-finiteness, and finite type
on the open locus. Added proof-only imports of Mathlib's quasi-finite morphisms and
`Sheaf.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs`.

The open neighbourhood is the image of the entire affine ring quasi-finite locus.
Thus the proof follows the direct open-set argument of Stacks Tag 01TI rather than
choosing a principal localization. The final assertion is proved through local finite
type and the stalk-map/isolated-fibre criteria. Updated the existing node's proof,
proof dependencies, and proof origin to record this argument. No definitions,
public signatures, other modules, or change records were needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAtPoint`
(node `lem-sc-quasi-finite-points-open`). Added 0 holes; split off 0 statements.
There are no remaining `sorry` declarations in the delivered module and no new modules.
All four private helper theorems have complete proofs.

Validation: the complete proof was compiled through `lcompile.py`. The theorem includes
arbitrary scheme morphisms: no global finite-type assumption was added. In particular,
the empty locus and empty source are covered by the pointwise local arguments.

## No longer needed

None: no imports or dependency nodes were removed. The three original declared
dependencies are all used: the Stacks quasi-finite predicates, affine spectrum charts,
and the ring quasi-finite locus theorem. Only the first (openness) clause of the latter
is required; its principal-localization witnesses are unnecessary in this proof.
The additional affine-pair dependency is already proved in the shared library.
No unit statement or realized proof step was bypassed; the assigned unit's realized
lists are empty.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The earlier plan unnecessarily chose a
basic localization after the ring theorem already supplied the required open subset.
The final assertion requires care because Mathlib's stalk-map quasi-finiteness omits
finite type. The proof establishes local finite type on the restricted locus separately
before invoking the isolated-fibre criterion, then recovers the exact Stacks predicate.
The node now records these details and the existing affine-pair theorem it uses.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
