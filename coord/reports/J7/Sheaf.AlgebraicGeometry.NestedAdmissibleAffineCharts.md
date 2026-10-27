## What changed

Proved `AlgebraicGeometry.SmoothOfRelativeDimension.exists_nested_admissible_affine_charts`
with its statement unchanged. A proved private lemma `nestedLocalCharts` applies the
existing local smooth normal form twice, transports an affine open of the restriction
back to X by its open-image isomorphism, and extends the second chart to affine space
above the original V. A proved private construction `orderedAffineIso` concatenates the
d outer coordinates followed by the e base coordinates and supplies an explicit inverse.
Pullback stability and composition give the two further etale assertions. Projection
identities give the composite factorization. Mathlib instances and proved private helper lemmas establish the structural
properties of all seven spaces and the admissibility of all seventeen arrows.

The item privately imports the proved local normal-form API from
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`. The DAG proof and dependencies
now follow this argument. The theorem type, public imports, and all other modules
are unchanged.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.SmoothOfRelativeDimension.exists_nested_admissible_affine_charts`
(node `lem-sp-nested-affine-charts`). Added zero holes; split off zero statements.
There are no `sorry` declarations left in the delivered module.

## No longer needed

Removed the private import `Sheaf.AlgebraicGeometry.SmoothAdmissibleCoordinateCover`:
only pointwise local normal forms are needed, without choosing finite covers.
Also removed unused private imports `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
`Mathlib.AlgebraicGeometry.Morphisms.Immersion`, and
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
The proof no longer directly needs `lem-sp-smooth-admissible-coordinate-cover`,
`lem-weil-pbc-qc-open-immersion-finite-type`, `lem-weil-pbc-separated-cancellation`,
`def-weil-affine-spectrum`, `def-weil-finite-type-morphism`,
`lem-weil-pbc-qcqs-over-affine`, or `pqf-lem-lft-fp-locnoeth` as proof dependencies.
Original statement dependencies remain unchanged. The obsolete coordinate-cover tool-use entry is
withdrawn; the relative-dimension permanence approval is retained because restriction uses it.
No module is withdrawn, and this report makes no claim that these dependencies lack
other consumers.

## Where the brief, the DAG or earlier work was wrong

The planned two applications of the finite coordinate-cover theorem are unnecessary:
two applications of the already-proved local normal form give the pointwise assertion.
No characteristic instance for `D.k`, or use of the coefficient prime, is needed.
The existing theorem docstring retains its original plan; the updated DAG and Lean proof
record the shorter route. No statement was disputed or changed. Empty X is vacuous;
d=0 or e=0 is covered by the same explicit coordinate concatenation and its inverse.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
