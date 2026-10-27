## What changed

Proved the vertical and horizontal coefficient-component naturality theorems in
`Sheaf.TraceFormula.AutomorphismTensorReductionComparison` without changing their
statements or any definitions. The vertical proof computes the identity-index map
using the functor identity law before applying finite coefficient naturality.
This avoids unfolding the concrete quotient sequence during unification.
The horizontal proof uses the existing coefficient-diagram naturality, the generic
horizontal restriction calculation, and a proved private helper identifying the
forgotten commutative coefficient sequence with the ring coefficient sequence.
Added a proof-only `import all` of
`Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison` to use its proved
coefficient-diagram map. Updated the horizontal node's proof dependencies.

## Proved and sorry left

Closed 2 of the 3 original holes:

- `WeilConjectures.trfAutomorphismCoefficientComponent_vertical`
  (`lem-trf-automorphism-coefficient-component-vertical`).
- `WeilConjectures.trfAutomorphismCoefficientComponent_horizontal`
  (`lem-trf-automorphism-coefficient-component-horizontal`).

One original hole remains, unchanged:
`WeilConjectures.trfAutomorphismTensorEvaluation`
(`lem-trf-automorphism-tensor-reduction-comparison`).
Added zero holes and split off zero statements. The main comparison theorem's
existing complete proof now uses the proved naturality clauses.

## No longer needed

None. No imports, modules, or planned dependencies were removed.

## Where the brief, the DAG or earlier work was wrong

The retained attempt unfolded the coefficient sequence before simplifying the
identity index map, causing a heartbeat timeout and exceeding 60 seconds. Its
final naturality application also had the wrong orientation. Both are repaired
using the functor identity law and the directly oriented naturality equation.
The horizontal clause can use the already proved coefficientDiagramMap instead
of reproving its constant-sheaf normalization argument.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
