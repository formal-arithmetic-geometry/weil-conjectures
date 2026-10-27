## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.completedCechTensorTransport` by a
proof from an ordinary module tensor comparison. The proof uses the existing
`HomologicalComplex.mapBifunctorComparisonNatTrans` and its summand formula,
constructs the chain isomorphism from the specified coefficient round trip, and
proves the displayed Koszul-unit equation by naturality and cancellation.
A proved private helper `tensor_unit_iso_cancel` checks whisker exchange, unitor
naturality and inverse cancellation abstractly, avoiding repeated unfolding of
the scheme-specific coefficient constructions.
The statement, universes, hypotheses and public import of the item are unchanged.

Added `Sheaf.Paper.WeilCompletedModuleTensorTransport`, containing the ordinary
bifunctor comparison and its regular-module normalization. This is the first
step of the existing node proof, separated from its complex-level second step.
It has no complex, totalization, Koszul parameter, or round-trip condition.
The proof locally prevents unfolding of the large coefficient/site equivalences
and uses a scoped heartbeat allowance for elaborating the comparison; the
60-second compiler limit is unchanged.
Private proof imports are the new module, the adopted homological comparison
API, and `import all Sheaf.AlgebraicGeometry.ProEtaleOperations` for the proved
coefficient equivalence. No source-library declaration was changed.

## Proved and sorry left

Original hole discharged by a reduction:
`AlgebraicGeometry.Scheme.completedCechTensorTransport`, node
`lem-weil-pbc-completed-cech-tensor-transport`. There is no sorry in its proof.

One hole added and still open:
`AlgebraicGeometry.Scheme.completedCechModuleTensorTransport`, node
`lem-weil-pbc-completed-module-tensor-transport`, in its own new module. Its proof
is exactly `:= by sorry`. Its docstring gives the balanced-tensor construction,
site reindexing, sheafification, inverse equations and unit calculation.

Counts: one original hole, one discharged, one added; this is a decomposition,
not a net proof. There are zero holes in the item and one in the new module.
No definitions have holes and no axiom declarations are introduced.

## No longer needed

No original imports were removed. No original declared dependencies or modules
are pruned: the completed site, intrinsic completion, tensor totalization, and
ringed Koszul system remain necessary. The existing ring-isomorphism derived
transport package was examined but is not imported: it supplies coefficient
transport, while a site comparison would still be required, and the parent needs
only the ordinary bifunctor comparison plus the existing totalization API.
The new ordinary node depends on ordinary sheaf tensor, not on complex tensor
or the Koszul system. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no definition was repaired. The original DAG
plan is mathematically valid; its first step is the remaining ordinary sheaf
tensor comparison. The totalization and normalized unit glue in its second step
are implemented in the item rather than left as another existential comparison.
The unit condition is independent of the Koszul model: naturality transports any
regular-module map, and the parent then specializes it to the named UnitZero.
The ordinary statement was checked on the zero ring, zero modules, the empty
site, and the regular-module unit. The parent covers arbitrary unbounded
complexes through the coproduct comparison and additivity.

## New nodes

`lem-weil-pbc-completed-module-tensor-transport`, in
`dag/nodes/sec-proper-base-change/`, states the ordinary module bifunctor
isomorphism and normalized right-unit equation, the first step of the original
proof. It is strictly below the item: it contains no complexes and does not
assert the item under a different name. The parent supplies the actual chain
isomorphism, identifies its first factor via the prescribed round trip, and
proves the Koszul-unit equation. The parent node proof and proof dependencies
are updated to this implementation. No existing definition or statement changed,
so there are no change records or forced adaptations.

The original theorem signature is checked against the shared source using the
project declaration parser. Both node dependency unions and Lean statement
attachments were checked against the delivered files. The final remote compile passed without warnings: the ordinary module took
5.6 seconds and the assigned module 42.9 seconds. The delivery tool records
its independent compile and preflight results.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
