## What changed

Proved `ordinaryFiniteDiagonalChartMap_eq_generic` from a generic chart-transport identification lemma. Added the strictly more general intermediate theorem `ordinaryFiniteChartTransport_eq_derivedChartCoefficientMap`, which remains a named proof obligation.

## Proved and sorry left

Closed the original `ordinaryFiniteDiagonalChartMap_eq_generic` hole. One sorry remains in `ordinaryFiniteChartTransport_eq_derivedChartCoefficientMap`; it is the generic four-factor identification used by the target.

## No longer needed

The attempted direct meta-level congruence route and the `CupProductCoherence` import are not needed by the delivered reduction. No DAG dependency beyond the two declared construction modules is used.

## Where the brief, the DAG or earlier work was wrong

The blueprint proof describes a generic four-factor equality, while the item statement specializes it to the diagonal chart. The generic equality is therefore split out as the strictly more general intermediate step so the specialization is a complete Lean proof.

## New nodes

`lem-z8-ordinary-finite-chart-transport-generic` records the intermediate theorem and its remaining proof obligation.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
