## What changed

Restored Sheaf.AlgebraicGeometry.SfP1ChartExchange from its recorded quarantine path.
Adapted the complete existing proof to the changed explicit object field of
ordinaryFiniteSingleFunctor: expose its projection locally and normalize shifted-line
composition with a proved private singleFunctor_obj equation instead of unfolding
ordinaryFiniteDegreeZero alone. All public signatures, definition bodies and imports
are preserved. The item's node retains its Lean attachment and every dependency;
its proof-origin note records the restoration. The restored item compiles cleanly
in 29.0 seconds with lcompile.py. A four-file compatibility compile also passed:
SfP1ChartExchange (50.7 s), SfP1ProjectionTraceTransportFalse (30.0 s),
SfP1ProjectionTraceTransportTrue (29.7 s), and SfP1ProjectionTraceTransport (30.2 s).
The three unchanged importer copies were removed after checking. See
coord/changes/B2-sf-p1-chart-exchange-degree-zero.md.

## Proved and sorry left

This is a compilation repair of an item with zero original holes. Holes closed: none
(0 of 0). Holes added: none. Holes left in this module: none. The chartExchange proof
and its existing private coherence proofs are preserved, with shiftedLine_comp adapted
to the new object interface. The new private singleFunctor_obj equation is proved by rfl.
Existing imported obligations, including chartMap_compHom, remain with their own nodes;
this packet neither moves nor adds their holes.

## No longer needed

None. No imports, modules, declarations, nodes or proof dependencies are pruned.
The unit route and the quarantined parent dependencies are preserved.

## Where the brief, the DAG or earlier work was wrong

The archived module already contained a complete proof; its current assignment is the
rework-table compilation repair after X7's degree-zero interface change, rather than a
new proof of a sorry. Marking ordinaryFiniteSingleFunctor irreducible was compatible
with its old body but hides the object projection of its new cached-functor body.
No mathematical statement or DAG proof route needs correction.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
