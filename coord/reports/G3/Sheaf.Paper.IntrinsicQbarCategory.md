## What changed

Completed `WeilConjectures.intrinsicQbarScalarCompatible` in
`Sheaf.Paper.IntrinsicQbarCategory`. The private proved helper
`rationalScalar_map_smul` derives semilinearity from the existing
`sfRationalScalarExtension_existsUnique` specification: turn its pure-tensor
HEq into conjugation along its prescribed object equalities, use bilinearity
of composition, and extend by tensor induction and additivity. The main proof
uses the recorded stage-system transition equation and cancels the normalized
localization and Shrink equivalences. Public signatures, definitions, instances,
and imports are unchanged.

Validation: the delivery dry run compiles without warnings, checks every local
declaration with the axiom probe, and passes the server preflight as `AUTO`.

## Proved and sorry left

Closed the one remaining hole:
`WeilConjectures.intrinsicQbarScalarCompatible`
(node `def-weil-pbc-qbar-category`). Added zero holes; split off zero statements.
The item has zero textual `sorry`s. The already landed proof of
`WeilConjectures.intrinsicQbarLinear_existsUnique` is retained unchanged and is
not counted as work of this delivery. Existing imported proof obligations remain
with their owning modules; no axioms or arbitrary data witnesses are introduced.

## No longer needed

None. Both existing public imports provide the published interface and remain
necessary. No imports, nodes, or modules are added or removed. The argument
implements the scalar-compatibility proof already documented on the declaration;
it does not change the blueprint unit route or introduce a new dependency route.
The searches preserved in `searches.jsonl` found general localization linearity
infrastructure, but no direct theorem for these intrinsic coefficient transitions.

## Where the brief, the DAG or earlier work was wrong

The initial brief predated the Z8 landing proving
`intrinsicQbarLinear_existsUnique`; the current baseline has only the scalar
compatibility hole. Earlier compile attempts received no server answer, so their
candidate proof had not been verified. Resuming compilation exposed a missing
explicit categorical bilinearity calculation in the pure-tensor case, now supplied
with the two composition rewrites in the correct order. Removed the unnecessary
local heartbeat setting to satisfy the style linter.
No mathematical statement or definition repair was required.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
