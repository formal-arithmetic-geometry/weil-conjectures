## What changed

Proved `AlgebraicGeometry.ProEtale.SpShriekTransition.coefficientMap_eq` by comparing
ordinary coefficient diagrams. The identity-component natural transformation is checked
on adjacent arrows with `NatTrans.ofOpSequence`; its naturality gives every composite
quotient map, including equal indices. ULift and constant sheafification act functorially.
All public declarations, their signatures, and the scalar-coordinate definitions are retained.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.SpShriekTransition.coefficientMap_eq`.
Remaining: `AlgebraicGeometry.ProEtale.SpShriekTransition.shriek_normalized_transition_comparison`
(node `lem-sp-shriek-normalized-transition-comparison`).
One of two original holes closed; zero holes added; zero split-off statements.
The remaining theorem keeps its original source and complete five-step proof docstring.

## No longer needed

None. The remaining main theorem retains its open/proper transition proof route and
all declared dependencies. No module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error found. Generic reduction naturality is an adjunction transpose
of the actual derived transition's naturality. The generic reduction cocycle already
exists in `SemilinearSections.Data`. The unresolved part of the main theorem is the
transport of the generic geometric formulas through the dependent constant-coefficient
identifications, and the identification of their specified mates with the open/proper
coefficient word. These are not inferred from faithfulness of derived evaluations.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
