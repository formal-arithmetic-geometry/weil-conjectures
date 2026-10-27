## What changed

Proved `AlgebraicGeometry.MarkedIdeal.transverse_suspension_rank_zero` in the assigned
module. The proof uses Mathlib's isomorphism instance for affine space on an empty
coordinate type, the zero-section pullback, and the retraction identity. On affine
opens the empty normal-coordinate family generates the zero ideal, proving the stated
ideal equality for every marking `b`, including zero. Empty schemes require no separate
nonemptiness assumption. Updated the theorem docstring and node Step 12 with this proof.

This is a partial delivery of the module: the main comparison theorem and the
admissible-chart theorem retain their original complete statements and proof plans.
Removed the 16 unused private imports listed below. Public imports, definitions,
and all declaration signatures are unchanged. No other existing module is changed.

## Proved and sorry left

Closed 1 of the original 3 holes:
`AlgebraicGeometry.MarkedIdeal.transverse_suspension_rank_zero`.
Added 0 holes; split off 0 statements.

The 2 remaining holes are unchanged whole theorem proofs, both attached to
`lem-trf-marked-ideal-transverse-suspension`:

- `AlgebraicGeometry.MarkedIdeal.transverse_suspension`.
- `AlgebraicGeometry.MarkedIdeal.transverse_suspension_admissible_charts`.

The completed proof is elementary and does not use these remaining theorems or
any unproved geometric dependency.

## No longer needed

The rank-zero proof needs none of the node's geometric proof dependencies.
Removed these unused private imports:

- `Sheaf.RingTheory.RegularSequenceGradedPolynomial`.
- `Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates`.
- `Sheaf.AlgebraicGeometry.SmoothPairRegularEquations`.
- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`.
- `Sheaf.TraceFormula.EtaleLocalRingFlatness`.
- `Sheaf.AlgebraicGeometry.PermissibleCoordinateChart`.
- `Sheaf.AlgebraicGeometry.StrictTransformFlatBaseChange`.
- `Mathlib.RingTheory.Unramified.LocalRing`.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`.
- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`.
- `WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence`.
- `WeilConjectures.AlgebraicGeometry.Regular`.
- `WeilConjectures.Blowup.Affine.Principalization`.
- `WeilConjectures.Blowup.FiniteDegree.Algebra`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `WeilConjectures.Blowup.FlatBaseChange`.

No DAG node or module is claimed globally pruned: the dependencies of Steps 1--11
are retained in `proof_deps` for the two untouched holes. The rank-zero proof uses
only the existing public imports. No declaration or module is withdrawn.

Searches run through `msearch.py`: LeanFinder for empty-coordinate affine space and
pullback of an isomorphism found the Mathlib affine-space isomorphism instance;
Loogle found `CategoryTheory.IsPullback.isIso_fst_of_isIso`; the grep query
`AffineSpace.*IsEmpty|ofIdealTop_bot` returned no hits. Direct source searches found
`AffineSpace.homOfVector_over`, `IsIso.of_isIso_comp_right`, and
`isIso_of_hom_comp_eq_id`. No equivalent proof of the two geometric theorems
was found in the source-library and Sheaf searches.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. Step 12's informal identification `N = Z`
is implemented as an isomorphism using the cartesian zero-section square; it does
not require equality of the scheme objects. The 16 original private proof imports
were not used by any existing proof and are unnecessary for the rank-zero proof.
The geometric dependencies and the unit route are retained for the unfinished parts.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
