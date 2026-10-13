## What changed

Added `SingleComplexOpenUnionSESCore`, which states the strict chain-model construction as a
strictly simpler intermediate theorem. The target theorem is proved from that data using
`cone_diagram_ses_presentation`, with the six comparison isomorphisms composed.

## Proved and sorry left

`singleComplexOpenComparison_union_ses_objects` is proved. The new intermediate theorem
`singleComplexOpenComparison_union_ses_core` remains a sorry, with node
`new-single-complex-open-union-ses-core`.

## No longer needed

None of the target's original imports were removed. `prop-pur-kinjective-resolutions-exist`
is recorded as the source dependency of the new intermediate construction.

## Where the brief, the DAG or earlier work was wrong

The original node's single construction step was too large to formalize directly in this
session; it is split into strict chain-model data followed by the generic mapping-cylinder
lemma. No statement was weakened.

## New nodes

`new-single-complex-open-union-ses-core`: strict chain maps and six derived-category
isomorphisms underlying the union construction. Node file:
`dag/nodes/sec-picard-framework/new-single-complex-open-union-ses-core.json`.

## Second reading by S2

1. **Interface check.** Compared the delivered target module with the repository version.
   The target declaration is byte-for-byte unchanged; only proof-only imports and the proof
   body were added. Verdict: pass.
2. **Proof check.** Compiled both sandbox modules with `lcompile.py --all`. The target proof
   has no `sorry`, and the only remaining hole is the named core theorem recorded below.
   No axiom, unsafe, opaque, extern, or hollow definition was introduced. The existing
   linter warnings concern unused existential binders already present in the target
   statement. Verdict: pass.
3. **Split statement check.** The core theorem is a strict lower-level chain-model
   construction, with a complete source and proof description and a matching DAG node. It
   is needed by the target proof and is not an existing library declaration. Verdict: pass.
4. **Pruning check.** The proof uses the generic cone-diagram presentation and the new core
   theorem; all retained imports are needed for declarations or proof elaboration. No old
   proof dependency can be removed without losing the unit route. Verdict: pass.
5. **DAG and unit check.** The target node's proof now follows the two applications shown in
   Lean, and the new node records the split construction and its dependency. The unit route
   through the union SES objects is retained. Verdict: pass.

Changed during second reading: renamed only local proof bindings that shadowed unused cone
data; no public statement or definition changed.

The proof-command change record is included at `coord/changes/single-complex-open-union-ses-objects-proof-commands.md`.
