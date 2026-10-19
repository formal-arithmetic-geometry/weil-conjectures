## What changed

Proved `IsDiscreteValuationRing.norm_valuation_sum` in
`Sheaf.RingTheory.DvrNormValuationSum`, with its signature and all public imports unchanged.
The proof follows Stacks Tag 02MJ: prove the formula for nonzero elements of B using the
stated lattice determinant and semilocal restriction theorems, then subtract the numerator
and denominator formulas. Three proved private helpers compare residue degrees, identify
localized principal quotients, and convert finite orders to logarithmic valuations.
Updated the existing node's proof, proof dependencies and proof origin to this route.
No definitions, existing signatures, consumers or other modules are changed.

## Proved and sorry left

Closed the one original hole: `IsDiscreteValuationRing.norm_valuation_sum`
(node `lem-exc-dvr-norm-valuation-sum`). No holes remain in the delivered module;
no holes are added and no statements are split off.
The proof uses the existing stated theorems
`IsDiscreteValuationRing.lattice_distance_determinant` and
`semilocal_restriction_length`; their existing holes are unchanged.

## No longer needed

The direct proof imports removed are:

- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`.
- `Mathlib.RingTheory.Length`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`.
- `Mathlib.Algebra.Module.LocalizedModule.Exact`.
- `Mathlib.RingTheory.PrincipalIdealDomain`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`.

Their definitions and instances that are still used are available through the retained imports.
Added proof imports are `Mathlib.Algebra.Module.LocalizedModule.Submodule`,
`Mathlib.Data.ENat.BigOperators`, and `Mathlib.RingTheory.Localization.Integral`.
Both original Sheaf proof imports remain necessary.

The explicit unit-times-uniformizer-power argument
(`lem-weil-pbc-dvr-unit-times-uniformizer-power`) and the explicit exact-sequence localization
step (`lem-weil-pbc-localization-module-exact`) are no longer direct dependencies of this
proof: Mathlib's fraction order and localized quotient APIs supply these calculations.
The six-step signed-intersection computation for arbitrary fractional y is unnecessary;
reducing to nonzero elements of B avoids localizing intersections and handles arbitrary
fractions by subtraction. No library modules are withdrawn. No blueprint unit step is bypassed.
The retained scratch experiment `SemilocalFractionLatticeDistance.lean` is outside lean/,
is not imported and is not part of the delivery.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and no mathematical error was found. The previous DAG route
used the full signed lattice distance for arbitrary fractions, although the cited proof of
Stacks Tag 02MJ first reduces to elements of B. The latter route needs less local glue.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
