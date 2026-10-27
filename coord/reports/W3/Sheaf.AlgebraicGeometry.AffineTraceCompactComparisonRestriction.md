## What changed

Filled `AlgebraicGeometry.Etale.affineTraceUnboundedCompactComparison_restriction`
using the existing compactification and composition restriction equations.
The zero case follows from the identity-pair composition equation and the left
unit laws, using naturality, cancellation and faithfulness. The successor case
pastes the line restriction square, two naturality squares, the induction
hypothesis and the composition restriction square.

Proved private categorical, identity and component helpers keep this calculation
abstract. The bounded-below successor isomorphism equation is isolated before
passing to components, avoiding direct reduction of the geometric composite.
The composition equation is also isolated at its native type before symmetry;
the pasting calculation then uses only component morphisms.
Updated the assigned node's proof and proof origin. Both original public imports,
all public signatures and all definitions are unchanged. No other library module
is modified.

Validation: the final Lean proof compiles without warnings through `lcompile.py`
in 12.9 seconds. All lines are at most 100 characters. The public comparison
definition, theorem signature and public imports match the original verbatim.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.affineTraceUnboundedCompactComparison_restriction`
(node `lem-amb-affine-trace-compact-comparison-restriction`).
All private helpers are proved. No holes remain in the item; no holes are added
or split off. This is a proof, not a decomposition.

## No longer needed

None. Both original imports and both declared proof dependencies are used.
No nodes or modules are withdrawn; the unit's ordered-coordinate induction is
preserved.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair is needed. The existing compact-support
comparison, composition restriction and identity unit declarations suffice.
The implementation uses the left unit laws for the identity pair; the prior
proof sketch described the equivalent argument with the right unit laws.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
