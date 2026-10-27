## What changed

Proved `AlgebraicTopology.orderedJoinPrefixTelescope` in
`Sheaf.AlgebraicTopology.OrderedJoinPrefixTelescope`, following all five steps of
`lem-sfb-ordered-join-prefix-telescope`. Private proved helpers establish the
empty prefix, composition through a list fold, and the successor prefix formula.
The local identity and square-zero differential imply remainder commutation;
induction gives prefix commutation; distributivity gives the homotopy summands;
Mathlib's reversed telescoping sum evaluates their sum. A separate list induction
proves invariance of each support subgroup and vanishing once a missing color is
encountered, then the assumed finite-sum generation gives the zero endomorphism.

Added only the private proof import `Mathlib.Algebra.BigOperators.Fin`.
All existing signatures, definitions, public imports, and docstrings are unchanged.
The proof follows the node's existing route, so no DAG changes are required.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicTopology.orderedJoinPrefixTelescope`.
Holes added: 0. Holes remaining: 0. Split off: 0.
Validation: the final single-file server compile passed without warnings in 4.2 seconds.
All five conclusion clauses are proved directly from the stated hypotheses and
Mathlib. No other project theorem with `sorry` is used.

## No longer needed

None. No original imports, nodes, or modules were removed. The only stated
proof dependency, `def-weil-pbc-module-chain-complex-homology`, is the Mathlib
complex API already publicly imported by the item and remains used.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The product order was checked
explicitly: in Lean, `P_(n+1) = R_n ≫ P_n`, representing the node's
`P_n ∘ R_n`. No commutation of different remainders is used. The cases of
empty prefixes, singleton color sets, empty supporting lists, zero-length
sum decompositions, and arbitrary integer degrees are covered by the proof.
The unit route is unchanged. The current blueprint paragraph (3) was read;
the node correctly labels this calculation as an agent expansion.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
