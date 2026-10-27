## What changed

Added the finite-free scalar projection intermediate `strictEtaleScalarTransportProjection` and reduced `etaleCoefficientSystemAdjoint_scalar` to its projection-to-exceptional-transport assembly. The intermediate isolates the target coefficient system, its adjoint, the three coefficient transports, and the finite-level mate-isomorphism data. The existing private geometric assembly theorem then constructs the final exceptional transport.

## Proved and sorry left

The original scalar theorem's `sorry` was decomposed into the named intermediate theorem `strictEtaleScalarTransportProjection`; its proof remains `sorry` because the finite-free scalar projection construction is the unresolved geometric step. The scalar theorem now has a complete Lean proof from that strictly smaller intermediate statement and `exceptionalTransportOfProjection`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The module's scalar theorem combines the finite-free coefficient transport construction with the exceptional-adjoint mate assembly. The latter is already a proved private categorical assembly, so the unresolved work is isolated as a separate projection statement.

## New nodes

`lem-pur-etale-scalar-transport-projection` records the intermediate statement and its source.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
