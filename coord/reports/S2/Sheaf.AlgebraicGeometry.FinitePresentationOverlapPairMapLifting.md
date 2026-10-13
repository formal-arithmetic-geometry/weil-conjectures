## What changed

Repaired the landing refusal from reviewer X-f6569. Removed the duplicate
`AlgebraicGeometry.overlapLimitMap_stage_comp` from the new shared module
`Sheaf.AlgebraicGeometry.OverlapPairCanonicalComparisons`. The existing public
lemma remains in its original module with identical signature and proof, and
is used by the main proof. The matching lemma in
`FinitePresentationOverlapCoherence` is private: importing that module would
not expose it. No private declaration is referenced by an internal name.

The new single-stage helper uses the elementary cone calculation directly for
the equality argument of `overlapIteratedComparison` in its statement. Proof
irrelevance identifies this argument with the original public lemma when the
main proof applies the helper. This adds no theorem or hole. The five shared
constructions keep their signatures, visibility and bodies. Updated their node,
the single-stage Lean statement record, and the relocation change record.

The original upper hole remains reduced to lifting at one stage and functorial
persistence under refinement. Both steps have separate modules, imported
privately by the item. Target signatures and all existing public interfaces
are preserved. The delivery dry run rebuilds its commit on current sheaf-dag.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_finitePresentation_overlap_pair_map_lifting`
(node `lem-pc-fp-overlap-pair-map-lifting`). No sorry remains in the item.

Two split-off holes remain:

- `AlgebraicGeometry.exists_overlap_pair_map_at_stage`
  (`lem-pc-fp-overlap-pair-single-stage`).
- `AlgebraicGeometry.overlap_pair_map_refinement_persistence`
  (`lem-pc-fp-overlap-pair-refinement-persistence`).

This is a decomposition: one upper hole closed, two lower holes added, net -1.
The main proof obtains a stage from the first helper and applies the second
helper after verifying the stage and limit composition triangles. No data
construction chooses an arbitrary witness of an unproved existence theorem.
The repair adds or closes no further holes.

## No longer needed

Removed the duplicate composition-lemma declaration from the new shared module;
its existing public declaration in the original item is retained and used.
The shared node now records five constructions, without that theorem.
No import of `FinitePresentationOverlapCoherence` is added: its private lemma
cannot supply the public interface, and its geometric coherence theorem is not
needed for this fixed-pair argument.

The item's old proof import `Sheaf.Algebra.FinitePresentationColimit` is removed
from the item and retained privately in the single-stage helper. Its node
`lem-pc-fp-module-map-descent-affine` remains needed there. No existing node or
module is claimed globally pruned. The earlier unlanded all-pairs restatement
`lem-pc-fp-overlap-pair-map-lifting-all-pairs` remains discarded.

## Where the brief, the DAG or earlier work was wrong

The prior relocation made the new shared module restate a theorem that also
appears privately in the coherence module. The landing checker refused it.
Keeping the existing public lemma in its original module and using an inline
proof argument in the new helper resolves that duplication without changing
another group's module or exposing a private theorem.

Earlier second readings apply to the previous delivery and have been removed;
a fresh second reader must review this repair. The unit
`sk-thm-picard-semicon` has empty realized lists. Its route is unchanged, and
the original lifting/gluing and subsequent refinement steps are retained.

## New nodes

`lem-pc-fp-overlap-pair-single-stage` states lifting and gluing at one stage
only, following Stacks Tags 01ZR and 05N7 (2), (3). Its equality proof argument
is now inline, with the same mathematical statement by proof irrelevance.

`lem-pc-fp-overlap-pair-refinement-persistence` states purely functorial
preservation of a given fixed-pair square; it has no finite-presentation or
limit assumptions and is unchanged in this repair.

`def-pc-overlap-pair-canonical-comparisons` records only the five existing
constructions relocated unchanged to avoid an import cycle. It adds no sorry;
the public composition lemma remains in the original item.

Change record: `coord/changes/overlapPairCanonicalComparisons.md`.
The item publicly re-exports the shared constructions. No downstream module
needs adaptation, and no forced adaptation is delivered.

## Second reading by S2

1. Compared the delivered item with the repository version. The target theorem
   signature is unchanged byte for byte; the five canonical constructions were
   relocated under the recorded change, and the composition lemma remains in
   place. Verdict: pass.
2. Compiled all four delivered modules with `lcompile.py --all`. The item has
   no remaining sorry; the only sorry declarations are the two named split-off
   theorems. No forbidden declarations or hollow definitions were found.
   Verdict: pass.
3. Checked the two split-off statements and their DAG nodes. Both are strict
   reductions of the target (single-stage lifting and functorial refinement),
   carry source and proof prose, and introduce no arbitrary witnesses. Searches
   found no existing declaration duplicating either statement. Verdict: pass.
4. The main proof follows the shortest available route through the two stated
   helpers; imports are private where used only by proofs, and the removed
   finite-presentation import is retained only by the single-stage helper.
   The shared canonical-comparison module prevents an import cycle. Verdict:
   pass; no additional pruning was found.
5. The DAG proof steps and dependencies match the Lean proof, and the unit's
   lifting then persistence route is retained. The canonical-comparison change
   record documents the interface relocation and its users. Verdict: pass.

Changed only the report during this second reading; no Lean declarations or DAG
statements required repair.
