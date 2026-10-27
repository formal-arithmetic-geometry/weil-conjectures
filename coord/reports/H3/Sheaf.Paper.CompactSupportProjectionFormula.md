## What changed

Decomposed `CompactSupportPbcProjection.tensor_identification` into three strictly
smaller named obligations in the same module: existence of the normalized tensor
isomorphism, equality of its ambient carrier, and equality of its Frobenius structure.
The parent theorem now proves the unique-isomorphism packaging and assembles these
three component results. No target signature or existing definition changed.

The three component theorems retain the proof plans from projection-formula step 13;
their proofs are postponed for parallel stage-3 work. The parent assembly compiles.

## Proved and sorry left

Closed one existing theorem hole by decomposition:

- `WeilConjectures.CompactSupportPbcProjection.tensor_identification`.

Added three strictly smaller named theorem holes:

- `WeilConjectures.CompactSupportPbcProjection.tensor_identification_exists`.
- `WeilConjectures.CompactSupportPbcProjection.tensor_identification_carrier`.
- `WeilConjectures.CompactSupportPbcProjection.tensor_identification_structure`.

The other three existing holes remain unchanged:

- `WeilConjectures.CompactSupportWeilProjection.openMate_isIso`.
- `WeilConjectures.CompactSupportWeilProjection.restriction`.
- `WeilConjectures.CompactSupportPbcTransport.bridge_existsUnique`.

The bridge statement remains marked `STATEMENT-DISPUTED` in the source module because
its displayed heterogeneous equality omits the inverse completion-tower comparison.

## No longer needed

None. The decomposition keeps the existing tensor comparison, coefficient transport,
finite-counit and Weil normalization dependencies. No import or DAG route is pruned.

## Where the brief, the DAG or earlier work was wrong

The original `tensor_identification` proof obligation bundled three independent
claims (existence with a prescribed arrow, ambient carrier equality, and Frobenius
structure equality) together with uniqueness. They are now exposed as separate
strictly smaller nodes so each can be proved independently. The bridge normalization
mismatch described in the existing `STATEMENT-DISPUTED` note is unchanged.

## New nodes

- `lem-sf-projection-tensor-identification-exists`: existence of the normalized
  tensor-presentation isomorphism with its prescribed underlying arrow.
- `lem-sf-projection-tensor-identification-carrier`: ambient carrier equality for the
  normalized completed tensor pair.
- `lem-sf-projection-tensor-identification-structure`: ambient Frobenius structure
  equality for the normalized completed tensor pair.

Each node records the projection-formula step-13 source, the three required search
records, and the exact Lean declaration attached to this module.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
