## What changed

Restored `lean/Sheaf/Paper/FdCoefficientComparison.lean` from the exact quarantine
path recorded in `coord/rework.tsv`. Repaired `FdOrdinaryScalarTransport.complex`
by giving the four existing functors explicit source and target module categories,
using their existing additive instances, ascribing the existing comparison to
those composites, and fixing the category arguments of the two composition
adapters. The same three canonical complex isomorphisms are composed in the same
order. No public imports, signatures, normalization clauses or coefficient maps
are changed, and no consumer adaptation is needed.

The change record is `coord/changes/A2-fd-coefficient-complex-additivity.md`.
The owning node `def-fd-coefficient-comparison-datum`, its Lean attachment and all
its dependencies are preserved. This is an elaboration repair, not a proof-route
change. The full repaired file compiles against the current library, exercising
both `completion` and the main structure's `chi` normalization.

## Proved and sorry left

Zero original holes; zero holes closed; zero holes added; zero holes left in the
restored item. No theorem is split off. This delivery repairs the assigned
zero-hole definition module rather than claiming a new mathematical proof.

## No longer needed

None. No imports, declarations, modules, nodes or dependencies are pruned.
The quarantined module and its downstream mathematical uses are retained.

## Where the brief, the DAG or earlier work was wrong

The archived definition depended on inference of the intermediate categories
when applying `Functor.mapHomologicalComplexCompIso` and mapping the ordinary
comparison to complexes. Current compilation fails to find additivity and
zero-morphism preservation there, despite the existing proofs. Supplying local
instances alone does not fix it; explicitly typing the intermediate functors and
categories does. The later missing `complex`, `completion`, and `finite_shift`
errors were consequences of this failed definition.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
