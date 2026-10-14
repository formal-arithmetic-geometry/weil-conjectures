## What changed

Completed `singletonTensorCech_coface_map_down` in the item's module. The proof identifies
its presheaf map as the universe lift of tensor-section restriction, then applies a
proved private calculation for an arbitrary additive map and constant product projection.
The helper accepts the index type's `Small` instance explicitly, preserving the caller's
chosen categorical product during specialization. All public statements, definitions,
and imports are unchanged. Updated the map-down node's proof and the parent node's
proof origin to record completion.

Change record: `coord/changes/S1-singleton-tensor-coface-proof-elaboration.md`
documents local transparency attributes and elaboration settings. These are scoped
to this module and preserve the public interface; no other module is adapted.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.Scheme.singletonTensorCech_coface_map_down`
(node `new-etale-singleton-tensor-cech-coface-map-down`).
Added zero holes; no `sorry` remains in the delivered module.
The existing proofs of `singletonTensorCech_coface_raw_projection` and
`singletonTensorCech_coface_evaluation` remain complete. All three new helpers are private
and fully proved. This is a proof, not a decomposition into new unproved statements.

## No longer needed

None. The sole public import supplies the definitions used by the public statements.
No additional dependency imports or DAG nodes were needed.

## Where the brief, the DAG or earlier work was wrong

The earlier timeout was not an obstruction to the stated elementary calculation.
A structural comparison of the original proposition with the inferred specialization
found different smallness witnesses for the tuple index: `small_Pi` in the original
statement and `UnivLE.small` in the helper. Those witnesses occur within chosen product
constructions; comparing the resulting expressions caused expensive kernel reduction.
Accepting `[Small.{u + 1} I]` explicitly in the private helper preserves the original
instance and makes the full proof compile quickly. No definition or interface repair
was required. The scoped unused-variable linter setting preserves the existing unused
`P` let-binding of the public statement; its statement is unchanged.

## Second reading by S1

1. Compared the delivered module with the repository version. All existing public
   declarations retain byte-for-byte identical statements; only local proof settings,
   private helper proofs, and the previously `sorry` proof changed. Verdict: pass.
2. Compiled the module with `lcompile.py` and checked for forbidden constructs and
   remaining local `sorry`s. The three public theorems compile; the only `sorryAx`
   dependency comes from still-open imported statements. Verdict: pass.
3. Reviewed the proof and DAG updates. The map-down proof uses definitional
   identification, a universe-lift calculation, and specialization; the evaluation
   theorem composes the raw projection and map-down results. No new public statement
   or split-off hole was added. Verdict: pass.
4. Checked pruning and imports. The sole public import remains needed for all stated
   definitions and theorem dependencies; no import can be removed. The unit route is
   preserved through the raw projection and map-down nodes. Verdict: pass.
5. Checked node metadata and proof records against the Lean proof, including the
   updated map-down proof steps and parent proof origin. Verdict: pass.

I changed only the report by adding this review section; no Lean source or DAG repair
was required.
