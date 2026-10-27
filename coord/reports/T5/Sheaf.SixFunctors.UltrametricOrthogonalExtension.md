## What changed

Proved `Padic.ultrametric_orthogonal_extension` in
`Sheaf.SixFunctors.UltrametricOrthogonalExtension`, preserving its entire signature.
Added the private proof import `Mathlib.LinearAlgebra.LinearIndependent.Lemmas`.

The proof bounds each residual distance below using `csInf_le`, rescales that
inequality for nonzero coefficients, and applies the ultrametric inequality twice
to obtain the two-term maximum formula. Splitting a `Fin (n + 1)` sum at its last
index gives the enlarged orthogonality formula. Residual non-membership in the old
span gives independence by `LinearIndependent.finSnoc`. Two submodule inclusions
give the span equality. The same proof handles `n = 0`; the coefficient-zero case
is handled separately before inversion.

Updated step 5 of `lem-sfb-ultrametric-orthogonal-extension` to record the direct
algebraic independence criterion. All proof dependencies remain empty; the only
statement dependency remains the coefficient-extension definition.

## Proved and sorry left

Closed 1 of 1 holes: `Padic.ultrametric_orthogonal_extension`
(node `lem-sfb-ultrametric-orthogonal-extension`). No holes remain in the item;
no holes or split statements were added.

The prescribed single-file server compile passed without warnings.
An explicit `#print axioms Padic.ultrametric_orthogonal_extension` check reported
exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No existing imports, nodes, or modules are pruned. The node has no planned
proof-dependency modules. Its coordinatewise independence calculation is replaced
by Mathlib's `LinearIndependent.finSnoc`; the norm and span arguments are retained.
A trial explicit import of `Mathlib.Algebra.BigOperators.Fin` was removed after
compilation showed it unnecessary.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was needed. The DAG's independence argument can
be shortened using residual non-membership in the span. The blueprint unit route
is preserved; no unit statement or realized proof step is bypassed.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
