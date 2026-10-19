## What changed

Proved `AlgebraicGeometry.ProEtale.cbcComparison_pullback_coherent` by specializing
`comparison_pullback_coherent` separately for sets, abelian groups, and modules.
The module clause explicitly introduces both the ring and finite instances. This
repairs the recorded Y7 global-build failure: applying the whole conjunction directly
did not introduce the extra `[Finite Λ]` binder.

The predicate `cbcComparisonPullbackCoherent` now abbreviates the existing canonical
`ComparisonPullbackCoherent`. Its identity and composition equations are identical;
the canonical bundled square clause expands to the same original chosen-square
equation, including its commutativity transport. All fifteen compact-support
constructions, their signatures, bodies and visibility are unchanged. The original
public imports are retained; the canonical coherence module is added publicly because
its predicate occurs in the public abbreviation. No target signature changes.

The existing DAG node records this reuse of the already proved four-step argument.
Change record: `coord/changes/cbc-comparison-coherence-specialization.md`.

Validation: the repaired item compiles in 7.1 seconds. Both unchanged direct
consumers compile against the freshly rebuilt sandbox artifact:
`FiniteConstantCoefficientTransport` in 52.1 seconds and
`PbcUniformCompleteTriangulated` in 6.0 seconds. No forced adaptations are needed.
The delivery tool also checks every delivered declaration's axioms.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.ProEtale.cbcComparison_pullback_coherent`
(node `lem-weil-pbc-comparison-pullback`). No holes remain in the item.
Added 0 holes; split off 0 statements.

## No longer needed

No modules or mathematical dependency nodes are pruned. The existing canonical
proof performs the same four DAG steps, preserving the unit route. Original public
imports remain for the consumers' elaboration context. No new modules or intermediate
statements are needed.

## Where the brief, the DAG or earlier work was wrong

The Y7 repair applied a theorem whose module clause no longer has a `Finite` binder
to a goal whose clause retains it. Coefficientwise specialization fixes that mismatch
without changing the compact-support theorem's signature.

The item duplicated an already proved canonical coherence theorem. Sharing that
predicate avoids a second large conversion of the expanded square equation. An
initial interrupted sandbox attempt also abbreviated all the constructions and
removed public imports; this packet retains their original bodies and import context.
A fresh compiled overlay is required when checking consumers: a single-file compile
does not refresh an existing sandbox output by itself.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
