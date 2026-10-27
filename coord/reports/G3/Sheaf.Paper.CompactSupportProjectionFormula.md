## What changed

Proved two remaining tensor identification components in
`Sheaf.Paper.CompactSupportProjectionFormula`, without changing any statement,
definition, visibility, attribute or public import. Added the proof-only
`import all Sheaf.Paper.ProjectionWeilTensorDomainBridge` to reuse its proved
private normalization helpers. Updated the two attached DAG nodes to record
this shorter existing route.

The carrier proof evaluates `normalized_tensor` on the two rational carriers.
The structure proof applies `rational_weil_tensor_structure` using
`normalized_tensor` and `normalized_mu`. These helpers handle arbitrary rational
Weil arrows, so neither proof assumes an integral lift of a Weil isomorphism.

Validation: the complete item compiled through `lcompile.py` in 26.3 seconds
(exit 0). No new modules or interface changes; no consumer adaptations required.

## Proved and sorry left

Closed 2 of the original 6 holes:

- `WeilConjectures.CompactSupportPbcProjection.tensor_identification_carrier`
  (`lem-sf-projection-tensor-identification-carrier`).
- `WeilConjectures.CompactSupportPbcProjection.tensor_identification_structure`
  (`lem-sf-projection-tensor-identification-structure`).

Added 0 holes and split off 0 statements. Four original holes remain unchanged:

- `WeilConjectures.CompactSupportWeilProjection.openMate_isIso`
  (`fix-prop-projection-formula`).
- `WeilConjectures.CompactSupportWeilProjection.restriction`
  (`fix-prop-projection-formula`).
- `WeilConjectures.CompactSupportPbcTransport.bridge_existsUnique`
  (`fix-prop-projection-formula`), already marked STATEMENT-DISPUTED in the source.
- `WeilConjectures.CompactSupportPbcProjection.tensor_identification_exists`
  (`lem-sf-projection-tensor-identification-exists`).

This is a partial proof delivery, with two holes closed and no decomposition.

## No longer needed

No imports, modules or nodes are withdrawn. Every existing import serves an
existing statement, definition or proof, and the new proof-only import supplies
all three normalization/transport helpers used here.

The two component nodes no longer require a new direct proof from just
`def-wf-weil-category` and `def-wf-tensor-product`: their needed comparison work
already exists in `lem-sf-projection-weil-tensor-domain-bridge`. Those definition
nodes remain statement dependencies and are not globally pruned. The unit route
and the other unfinished projection arguments are retained.

## Where the brief, the DAG or earlier work was wrong

The two component proof plans overlooked the already proved private
normalization helpers in `ProjectionWeilTensorDomainBridge`. Reusing them
closes both holes directly.

The existing STATEMENT-DISPUTED notice at
`CompactSupportPbcTransport.bridge_existsUnique` remains: its displayed raw
integral normalization omits the inverse actual-completion/tower comparison,
so the two claimed HEq source objects are not identified by that isomorphism.
This delivery does not use that disputed theorem in either new proof and does
not attempt an interface repair of the remaining coefficient-presentation work.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
