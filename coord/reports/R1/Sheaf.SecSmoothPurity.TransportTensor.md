## What changed

Proved `AlgebraicGeometry.ProEtale.PurityTransport.line_flat` in
`Sheaf.SecSmoothPurity.TransportTensor`. The private proved helper
`flat_of_local_unit` descends flatness from a pro-etale cover by jointly reflecting
finite limit cones. The main proof uses the existing integral Tate local-basis
and internal scalar-extension flatness theorems, then induction on tensor powers.
Added only private proof imports; all existing signatures, public imports,
definitions and file-level options are unchanged. Updated the existing tensor
coordinate node's proof, dependencies and origin to describe this argument.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.PurityTransport.line_flat`
(node `def-pur-transport-tensor-coordinates`). The helper `flat_of_local_unit` is
fully proved. Holes closed: 1. Holes added: 0. No `sorry` remains in the item or
is added elsewhere. Existing dependency theorems retain their current proofs.
This is a proof from existing declarations, not a decomposition.

## No longer needed

None. There were no original proof dependencies or proof-only imports to prune.
The existing public imports and the unit route are preserved. In particular,
this proof does not need the normalized integral pullback comparison theorem:
it uses the local basis of the integral Tate module directly, while retaining
the existing public `TransportPull` interface import for its consumers.

## Where the brief, the DAG or earlier work was wrong

The tensor-coordinate node originally had no proof steps or proof dependencies
for its flatness assertion. Added the actual argument and named its existing
local-basis and scalar-flatness dependencies. No statement or definition repair
was needed. The empty scheme is covered by the same conservative-family argument
with an empty cover. The zero-power case is the tensor unit. The scalar-extension
step assumes no flatness or nonzero condition on the target coefficient ring.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
