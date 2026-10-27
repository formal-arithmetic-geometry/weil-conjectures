## What changed

Completed `Sheaf.FieldTheory.ValuationTopologyCommonCoarsening` without changing the public
statement or imports. Five proved private helpers reindex the ball basis by field units,
compare topologies by mutual ball refinement, bound elements of the generated subring,
construct the common proper coarsening, and obtain ball refinement from a coarsening.
Updated the item's node proof to describe the implemented argument.

The generated subring is the explicit `Subring.closure` of the union. Its valuation bound
uses an induction invariant: each element has value bounded by the value of an element of
the second valuation ring. Multiplication preserves this invariant by multiplying witnesses.
The proof works on the actual value groups and does not need the stated surjectivity
hypotheses; those hypotheses and every other public binder remain unchanged.

Searches with LeanFinder, Loogle, msearch grep, and local rg found valuation equivalence
results, which require equal valuation rings and do not prove the common-coarsening
criterion. Mathlib's existing valuation subrings and neighbourhood bases supply the APIs.

## Proved and sorry left

Closed 1 of 1 original holes:
`AddValuation.topology_eq_iff_exists_common_proper_coarsening`
(node `lem-per-valuation-topology-common-coarsening`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivery.

Validation: the complete proof compiled on the server in 3.5 seconds. The final delivery
check recompiles the warning cleanup and checks the axioms of every declaration.

## No longer needed

None. No imports, nodes, or modules were removed. The sole planned dependency,
`def-trf-valuation-ring`, is realized by Mathlib's `ValuationSubring` construction as before.
The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or broken dependency was found. The elementary proof can use balls
indexed by field units, so its explicit choices of arbitrary additive radii and the
surjectivity assumptions are unnecessary for the proof. A closure induction with a
variable witness replaces the DAG's finite-sum presentation of the same generated ring.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
