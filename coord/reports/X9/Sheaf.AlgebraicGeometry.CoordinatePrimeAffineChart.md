## What changed

Implemented `AlgebraicGeometry.coordinatePrimeAffineChart_realization` without changing
its statement or either chart definition. The proof establishes membership in the
basic opens, containment over D(f), the equation over Spec R_f, local finite type,
quasi-compactness, quasi-finiteness, finite discrete scheme fibres, the marked image
prime, and the base-point equation. A proved private helper obtains the ring-map
quasi-finiteness from compact discrete algebra fibre spectra.

The remaining residue-field computation is isolated in the new module
`Sheaf.AlgebraicGeometry.CoordinatePrimeResidueField`. Its theorem applies to a point
of localized affine space directly, independently of any source chart, finite-type
map, or quasi-finiteness assumption. The original theorem proves its hypothesis by
identifying the marked image prime and base point; it then applies this theorem.
This is the coordinate calculation of original proof steps 5–7, strictly part of the
original argument, rather than a renaming of the chart theorem.

The original DAG proof and proof dependencies are updated to match the implemented
argument. No existing shared module besides the assigned item is changed; its public
imports, definition bodies and declaration signatures are unchanged. No consumer
adaptations or change record are required.

## Proved and sorry left

Original holes: 1. Original direct hole removed:
`AlgebraicGeometry.coordinatePrimeAffineChart_realization`
(node `lem-trf-coordinate-prime-affine-chart-realization`). The combining proof is
complete, subject to the following strictly smaller residue-field theorem.

New holes: 1, exactly
`AlgebraicGeometry.coordinatePrimeAffineSpace_residueField`
(node `lem-trf-coordinate-prime-rational-residue-field`), in the new module
`Sheaf.AlgebraicGeometry.CoordinatePrimeResidueField`. Its proof is exactly
`:= by sorry`; its docstring gives the evaluation-kernel, fraction-field surjectivity
and structural-map compatibility argument with sources.

This is a decomposition, not a net hole closure: 1 upper hole removed, 1 lower hole
added, net 0. The item module itself has zero remaining direct holes. Its geometric
clauses and marked-prime computation are proved independently of the new theorem.
The private helper `quasiFinite_of_coordinate_chart_primes` has no holes.

Validation: lcompile.py --all passed for both modules in dependency order. The item
compiled in 6.4 s; the residue-field statement compiled in 2.6 s in the preceding
check and was reused in the final check. Existing signatures and public imports
compare identical. The delivery preflight also runs its compiler and axiom probes.

## No longer needed

Removed private proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties` (already available through
  the retained imports).
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated` (the direct Mathlib
  quasi-finite API supplies isolated fibre points).
- `WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso` (the marked prime
  uses the basic-open structural equation and Mathlib `IsLocalization.map_under`).
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC`
  (no structural residue-field calculation remains in the combining proof).

Removed direct DAG proof dependencies:
`lem-weil-pbc-lft-pointwise-criterion` (use the affine Spec criterion directly),
`lem-weil-pbc-quasi-finite-at-point-isolated` (use the Mathlib API), and
`lem-weil-pbc-localization-prime-residue-field-iso` (use Mathlib localization ideal
correspondence directly).

The direct dependencies `def-weil-pbc-mv-polynomial-ring`,
`lem-weil-pbc-prime-residue-field-algebra`,
`lem-weil-pbc-spec-residue-field-identification`, and
`lem-weil-pbc-spec-map-residue-field-naturality` move to the residue-field node:
their mathematics is still needed there, so no global pruning of them is claimed.
No modules or declarations are withdrawn, and no claim is made that a removed
private import is globally unreachable.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The planned pointwise affine neighbourhood
construction is unnecessary: primewise isolated algebra fibres, compactness and
Mathlib's affine criteria give the chart properties directly. No finite-presentation
or Noetherian hypothesis is introduced. The unit route is preserved.

The residue-field calculation has no exact Mathlib match: the available
`Polynomial.residueFieldMapCAlgEquiv` covers one variable and a prime extended from
the coefficient ring, rather than this localized multivariable coordinate prime
with its actual scheme structural-map compatibility.

## New nodes

`lem-trf-coordinate-prime-rational-residue-field` states the residue-field part of
original proof steps 5–7, with no source chart or quasi-finiteness data. Its module is
`Sheaf.AlgebraicGeometry.CoordinatePrimeResidueField`. Sources are Stacks 0520 and
the first paragraph of 052E, expanded using the residue-field universal property.
The node records the searches actually run with LeanFinder, LeanSearch, Loogle and
grep. Blueprint searches for coordinate primes and purely transcendental residue
fields found no equivalent imported blueprint statement.

Edge cases checked mathematically: r=0 gives the base field; r=n kills no variables;
n=0 is included in both; if f is nilpotent the localized affine space has no points
and the theorem is vacuous. For nonmaximal p, the image is proved to contain the
fraction field of R/p, so it is not incorrectly identified with R/p alone. The
isomorphism is required to commute with the actual residue-field map, which
excludes an arbitrary abstract field isomorphism.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
