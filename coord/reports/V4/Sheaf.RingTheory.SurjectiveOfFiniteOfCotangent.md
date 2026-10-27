## What changed

Proved `RingHom.surjective_of_finite_of_cotangent` in
`Sheaf.RingTheory.SurjectiveOfFiniteOfCotangent`, preserving its signature and public imports.
The proof follows all three steps of
`lem-sc-point-tangent-finite-local-cotangent-surjective`:
cotangent surjectivity gives `n ≤ mB + n²`; the finite-dimensional algebra `B/mB`
is Noetherian, so Nakayama kills the image of `n`; residue-field surjectivity and
Nakayama applied to the range of the finite `A`-module map give surjectivity of `f`.
The intermediate quotients and module structures are constructed explicitly.
No definitions, other modules, or DAG routes changed.

## Proved and sorry left

Closed the single original hole in `RingHom.surjective_of_finite_of_cotangent`
(node `lem-sc-point-tangent-finite-local-cotangent-surjective`).
Holes closed: 1. Holes added: 0. Holes remaining: 0. Split off: 0.
Both Nakayama applications use Mathlib; no project theorem containing `sorry` is used.
The module compiled without warnings using only its original imports.
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No original imports, declared dependencies, nodes, or modules are pruned.
The two existing Mathlib-leaf Nakayama dependencies remain needed.
The trial proof import `Mathlib.RingTheory.LocalRing.Quotient` was removed:
the original imports already provide all required declarations and instances.
No additional import is retained.

## Where the brief, the DAG or earlier work was wrong

None. The statement is valid without assuming the maximal ideal of `B` is
finitely generated: the required finite generation is proved after passing to `B/mB`.
The unit route and the node's existing proof plan are preserved.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
