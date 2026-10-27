## What changed

Filled `AlgebraicGeometry.Etale.ordinaryFiniteChartTransport_eq_derivedChartCoefficientMap`
without changing either public theorem statement, any import, or any shared definition.
The proof expands the chart construction aliases using private structural-congruence
metaprograms adapted from the existing `SfP1ChartMapComposition` proof. Every generated
proof is kernel checked; proposition arguments are compared by proof irrelevance, and
the derived localization constructions remain folded. The diagonal specialization
continues to apply this generic equality. Updated both attached nodes to match the proof.

The complete module compiled in a diagnostic copy in 10.7 seconds, without warnings.
The delivery tool checks the final module and its axiom dependencies.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Etale.ordinaryFiniteChartTransport_eq_derivedChartCoefficientMap`
(node `lem-z8-ordinary-finite-chart-transport-generic`).
Retained the complete proof of `AlgebraicGeometry.Etale.ordinaryFiniteDiagonalChartMap_eq_generic`.
Holes before: 1. Holes after: 0. Holes added: 0. No statements split off.

## No longer needed

No imports, modules or mathematical dependencies were pruned. Both construction modules
remain necessary for the statements. The diagonal node now records its actual application
of the generic equality instead of describing a direct expansion proof. No additional
proof import of `SfP1ChartMapComposition` is needed: only its private proof-building method
was adapted, without depending on its projective-line composition theorem.

## Where the brief, the DAG or earlier work was wrong

The mathematical four-factor identification is correct. Direct rewriting followed by
reflexivity, and direct application of the component equation, each exceeded the compile
limit while comparing the recorded category instances. The unchanged declarations compiled
in 7.3 seconds and the imports alone in 6.6 seconds, isolating this to proof elaboration.
Structural congruence closes the obligation without changing definitions or making another
split. The argument imposes no extra condition on the schemes, coefficient ring or arrows.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchangeAux": "a3a424f40b1464dc9ff07b6af1b9761a09040dbb"}, "results": {"Sheaf.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchange": {"hash": "551dba04d5308f38b1a3151918e8abc548460ef8", "status": "OK"}}, "seconds": 281, "time": "2026-10-27T23:35:04+0800", "transitive": 0, "version": 1}
```

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
