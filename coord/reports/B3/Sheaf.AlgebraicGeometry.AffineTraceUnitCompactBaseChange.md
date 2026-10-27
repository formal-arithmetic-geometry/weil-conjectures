## What changed

Reduced `AlgebraicGeometry.Etale.affineTraceUnitCompactComparison_baseChange` to the
bounded-below restriction of an explicitly constructed unbounded comparison. Its
statement and public imports are unchanged. The item now privately imports
`Sheaf.AlgebraicGeometry.AffineTraceCompactComparisonRestriction`.

The new module constructs `affineTraceUnboundedCompactComparison` recursively from
the compact-support identity, the standard line compactification comparisons and
the compact-support compositor. Its data contains no hole. The item proves exchange
compatibility of this comparison for every unbounded coefficient by induction.
Identity exchange follows from the composition equation, unit laws, cancellation
and faithfulness along the identity. Each successor uses compactification
independence, composition of exchange and naturality. Naturality at the canonical
coefficient isomorphism completes the original equation once the restriction
identity identifies its prescribed endpoint comparisons.

No existing module besides the item is changed. Experiments replacing recursion
bodies in shared definitions were restored; their compiled artifacts were cleared.
The item's node now records the actual proof and its one new dependency.
Both files compile without warnings against the published shared definitions:
43.4 seconds for the restriction module and 53.5 seconds for the item module.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.Etale.affineTraceUnitCompactComparison_baseChange`
(node `lem-amb-affine-trace-unit-compact-base-change`) is closed by a complete proof
from the restriction identity and the existing compact-support declarations.
All private helpers in the item are proved.

One hole is added:
`AlgebraicGeometry.Etale.affineTraceUnboundedCompactComparison_restriction`
in `Sheaf.AlgebraicGeometry.AffineTraceCompactComparisonRestriction`
(node `lem-amb-affine-trace-compact-comparison-restriction`).
Its source and complete induction argument are in the docstring and node.

Original holes closed: 1 of 1. Holes added: 1. Net holes closed: 0. This is a
decomposition, not a completed proof of the item without new dependencies. The
remaining statement concerns only comparison restriction; it has no morphism of
bases, exchange square, canonical Tate coefficient or base-change conclusion.
The unbounded exchange induction and its application to the coefficient map are
proved here, rather than moved to another hole.

## No longer needed

None. No original import, node or module is pruned. The four original proof
dependencies remain used. The proof calculates exchange directly on the unbounded
category, so it needs only the comparison restriction, not a separate restriction
identity for exchange.

## Where the brief, the DAG or earlier work was wrong

No statement error was found, and the unit route is preserved. The bounded-below
restriction step is more than an immediate conversion in Lean. A direct induction
was written through the compactification and composition restriction equations;
checking its comparison successor projection produced kernel deterministic
timeouts (about 100 seconds for the small projection alone). Local irreducibility,
abstract categorical pasting, explicit projection of generated equation lemmas,
and experiments with explicit Nat.rec bodies did not resolve the conversion cost.
All shared-definition experiments were restored. This delivery isolates exactly
that genuine part of the planned argument, with its full mathematical proof,
while retaining the separately proved exchange induction and naturality assembly.

## New nodes

`lem-amb-affine-trace-compact-comparison-restriction` states that the explicitly
constructed unbounded tower comparison restricts to the specified D+ comparison.
It is the comparison-restriction part of the original node's first proof step.
The new module also contains the real recursive construction it uses. The node
records the identity/unit calculation and successor pasting argument, the source,
three Mathlib searches, its two declared dependencies, and the exact Lean statement.
There are no change records, withdrawn modules or forced adaptations.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
