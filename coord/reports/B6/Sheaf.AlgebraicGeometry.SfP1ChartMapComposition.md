## What changed

Filled `AlgebraicGeometry.Etale.SfP1Transport.chartMap_compHom` in the item module.
The private helper `comp_congr` identifies direct-image composition followed by
congruence with the composite-adjunction comparison. It follows immediately by
substitution and `conjugateEquiv_leftDerivedUpperStarComp_hom`, imported privately
from `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat`.
The main proof evaluates this equality, composes with the mapped unit and line
comparison, and reassociates. A private congruence procedure reconciles recorded
instances using heterogeneous proof irrelevance and small definition expansions;
every generated proof term is checked by Lean's kernel. Public signatures,
public imports, shared definitions, and the node's proof route are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.SfP1Transport.chartMap_compHom`
(node `lem-sf-p1-chart-map-composition`).
Zero `sorry` remain in the item. Zero holes added, zero split off.
The complete single-file proof compiled in 38.8 seconds in the profiling run.
Profiling options were removed before delivery. The delivery tool performs the
final compile and axiom probe.

## No longer needed

None. No existing imports, declared proof dependencies, nodes, or modules are
pruned. The chart construction and its structural equation remain used, and the
unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

The current DAG argument is valid and is followed without a statement repair.
The chart-map definition packages its factors in `ordinaryFiniteChartTransport`
and `ordinaryFiniteAdjunction`; both wrappers are explicitly unfolded.
Direct simplification of the final equality was too expensive because of the
recorded category and monoidal instances. Explicit congruence, with
`proof_irrel_heq` for proof arguments, avoids expanding their proof types and
keeps the complete file within the compile limit. No shared definition repair
or new proof obligation was necessary.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
