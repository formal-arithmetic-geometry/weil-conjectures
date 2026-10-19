## What changed

Completed `arithmeticModelFiber_over` and `arithmeticLiftMap_basepoint`. Completed the
private finite-model injectivity, range, action, base-change injectivity, and combined-range
lemmas used by the arithmetic fibre construction. The main theorem remains open.

## Proved and sorry left

Proved: `arithmeticModelFiber_over`, `arithmeticLiftMap_basepoint`,
`arithmeticModelFiber_injective`, `arithmeticModelFiber_range`, `arithmeticModelFiber_action`,
`arithmeticBaseChange_injective`, and `arithmeticModelFiber_ranges`.

Closed 2 of the 3 original holes: `arithmeticModelFiber_over` and
`arithmeticLiftMap_basepoint`. Added 0 holes.

Sorry left: `arithmeticLiftFibrePath` (node `lem-wf-arithmetic-lift-fibre-path`) (the arithmetic quotient exact-sequence assembly and
natural semilinear fibre-path construction remain).

## No longer needed

None identified. The retained proof uses the existing imports and does not add modules or
nodes.

## Where the brief, the DAG or earlier work was wrong

The earlier expanded exploratory quotient and descent blocks exceeded the compiler limit.
The retained validated snapshot compiles within the limit; those exploratory blocks were
removed because they were not compiler-validated.

## New nodes

None.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
