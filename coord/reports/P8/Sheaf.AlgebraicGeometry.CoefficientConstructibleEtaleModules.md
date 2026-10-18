## What changed

Proved `AlgebraicGeometry.Scheme.coefficientEtaleBaseChange_isContinuous` in
`Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules`. The proof follows its
existing docstring: transport continuity along the AsSmall equivalence, use Mathlib's
`Scheme.isContinuous_overPullback` for etale base change, and compose twice with
`Functor.isContinuous_comp`. No signatures, definitions, visibility, or imports changed.

The single-file remote compile passes without warnings in 5.6 seconds. An additional
`#print axioms` check on the proved theorem reports exactly `propext`, `Classical.choice`,
and `Quot.sound`; the check command was removed from the delivered source.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.coefficientEtaleBaseChange_isContinuous`
(node `def-pe-etale-constructible-module`).

No sorry remains in the item module. No holes added and no statements split off.

## No longer needed

None. No imports, nodes, or modules were pruned. The three existing public imports
supply the retained constructibility interface, coefficient-sized sites and derived
cohomology, and constant-scalar restriction. The existing continuity plan is realized
using declarations already available through those imports; no proof import is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The attached node is a definition node with
empty proof and proof_deps fields; the supporting continuity theorem has its complete
three-functor argument in its existing docstring. This delivery implements that argument
without changing the definition node or the unit's route.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
