## What changed

Proved `AlgebraicGeometry.exists_open_prescribedPoint_nonzeroJets` in
`Sheaf.AlgebraicGeometry.PrescribedPointNonzeroJetOpen`, preserving its signature and public
import. Added proved private helpers for nonzero jet targets, scalar compatibility, the
coefficient-to-jet linear map, coefficient points in basic opens, and the finite intersection
construction. Updated the theorem docstring and the existing node to match this proof.
The private imports `WeilConjectures.Mathlib.Topology.Sober` and
`Mathlib.RingTheory.KrullDimension.Field` supply the generic-point criterion and the
dimension-zero theorem for fields; the remaining APIs come from the existing public import.

The proof uses the Noetherian cotangent field criterion and positive pure dimension for
nontriviality. It then uses a detecting linear functional at each point and intersects the
basic opens of the resulting linear polynomials. No finite-dimensionality or residue-field
comparison is needed. The empty prescribed set is covered by the same finite-intersection
argument.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.exists_open_prescribedPoint_nonzeroJets`
(node `lem-zl-prescribed-point-nonzero-jet-open`).

Holes added: none. Split-off statements: none. Sorries left in the delivered Lean: zero.
All private helpers have complete proofs.

Validation: the final file compiled cleanly through `lcompile.py` in 9.1 seconds, with
no errors or warnings. A source comparison confirms the theorem signature is unchanged;
all delivered Lean lines are at most 100 columns.

## No longer needed

The following planned proof dependencies are not needed by this theorem:

- `lem-weil-pbc-smooth-over-field-regular-local`
  (`Sheaf.RingTheory.SmoothOverFieldRegularLocal`).
- `lem-sc-regular-connected-integral`
  (`WeilConjectures.AlgebraicGeometry.Regular`).
- `lem-weil-pbc-smooth-over-field-dimension-differentials`
  (`WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension`).
- `lem-sc-integral-locally-algebraic-opens-dimension`
  (`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`).
- `lem-weil-pbc-maximal-ideal-differential-cotangent-dimension`
  (`WeilConjectures.AlgebraicGeometry.MaximalIdealDifferentialCotangentDimension`).
- `lem-kun-closed-point-field` (`Sheaf.AlgebraicGeometry.ClosedPointField`).

The cotangent field criterion replaces the regularity/dimension calculation, and separating
linear functionals replace finite-dimensional coordinates. These dependencies were not
imported in the original item, so no original import was removed. No module is withdrawn;
other consumers of these declarations are unaffected.

## Where the brief, the DAG or earlier work was wrong

The planned proof is mathematically valid but stronger than necessary: it computes the
cotangent dimension and identifies closed-point residue fields. Positive pure dimension,
local Noetherianity and linearity suffice. The preserved theorem interface still includes
smoothness, algebraic closedness, quasi-compactness and the commutative triangle, even though
the direct proof does not need all these hypotheses. The unit route is unchanged.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
