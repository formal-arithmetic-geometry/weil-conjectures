## What changed

Replaced the proposed `GrothendieckBottomAugmentationCore` restatement with a real
reduction of `CategoryTheory.grothendieckBottomEdge_augmentation` into two separate
parts. Its existing signature, visibility and docstring are unchanged.

Added `Sheaf.CategoryTheory.GrothendieckBottomEdgeSingleUnit`: the bottom edge is
homology of the derived unit, independent of all prescribed resolutions and comparison
maps. Added `Sheaf.CategoryTheory.ResolutionDerivedSingleUnitAugmentation`: a proved
derived-category equality transporting that unit to an augmented comparison. The
latter requires only enough injectives in A, no left exactness, no G, and no degree n.
The parent combines these equations using functoriality of RG and homology.
Both new imports in the existing module are plain, proof-only imports. The new
modules' public imports are needed by their signatures. Updated the parent's proof
plan and dependency list to follow the actual reduction.

## Proved and sorry left

Hole closed: `CategoryTheory.grothendieckBottomEdge_augmentation` (one of the one
original holes in the item), proved conditionally from the strictly smaller bottom-edge
identity and the proved resolution transport.

New proved theorem: `CategoryTheory.resolutionDerivedSingleUnit_augmentation`, node
`lem-sc-resolution-derived-single-unit-augmentation`. Its `#print axioms` lists only
`propext`, `Classical.choice`, `Quot.sound`.

Hole added and left: `CategoryTheory.grothendieckBottomEdge_singleUnit`, node
`lem-sc-grothendieck-bottom-edge-single-unit`, in its own module with a complete
natural-language proof and source. It is the only `sorry` in the delivered files.
The parent's axioms are the three standard axioms plus `sorryAx` from this lower hole;
the lower theorem's axioms have the same list. No data definitions were added.

This is a decomposition: one original hole closed, one strictly smaller hole added,
net zero holes removed. The original target is not axiom-free yet. The discarded
`CategoryTheory.grothendieckBottomEdge_augmentation_core` and its node were never
landed and are not part of this delivery or its hole accounting.

## No longer needed

No existing import or module is pruned. The original direct proof dependencies
`def-pc-canonical-resolution-derived-iso`, `lem-sp-derived-well-defined`, and
`lem-sp-grothendieck-edge-maps` are replaced as direct dependencies of the parent by
the two new nodes. All three remain needed transitively (and their notions occur in
the unchanged signature), so none is claimed pruned from the targets' closure.

The unlanded restatement module `Sheaf.CategoryTheory.GrothendieckBottomAugmentationCore`
and node `lem-sc-grothendieck-bottom-augmentation-core` were removed from the sandbox.

## Where the brief, the DAG or earlier work was wrong

The first worker's core theorem retained every hypothesis and the entire bottom-edge
conclusion; replacing two homology maps with homology of their composite changes
nothing except functoriality. Its earlier review's claim that this was a strictly
smaller derived-category factor was incorrect. The proposed delivery also did not
update the parent node to describe its proof. The second reading replaces that
restatement with an actual bottom-edge identification plus a fully proved resolution
transport, and aligns the DAG with them.

LeanSearch returned Internal Server Error; this is recorded as unavailable. Loogle,
Lean Finder, and local searches found the unit and truncation building blocks but
no existing theorem for either displayed equation. The existing
`rightDerivedPlusSingleUnit` definition is reused, never redefined.

## New nodes

`lem-sc-grothendieck-bottom-edge-single-unit` records the bottom-interval/unit
identification in `Sheaf.CategoryTheory.GrothendieckBottomEdgeSingleUnit`. Its
statement has no I, J, phi, augmentation hypothesis, or resolution-derived isomorphism;
its remaining proof is the canonical truncation normalization and zero-shift computation.

`lem-sc-resolution-derived-single-unit-augmentation` records the proved resolution
transport in `Sheaf.CategoryTheory.ResolutionDerivedSingleUnitAugmentation`. Its proof
uses derived-unit naturality, cancellation on the injective complex, degree-zero
complex extensionality and localization. It has no spectral sequence or G.

No change record is required: no existing statement or definition changed.

## Second reading by F3

1. Compared the delivered parent with the repository using `diff`. Its existing
   declaration signature is byte for byte unchanged; only its proof and two plain
   imports differ. The new declarations have their own modules. No other existing
   Lean module is delivered, and no definition or target statement is altered. Pass.
2. Compiled all three modules through `lcompile.py --all` in import order, without
   errors or warnings. Compiled scratch copies with `#print axioms` for all three
   theorems. The resolution transport has only the three standard axioms; the parent
   and the named lower hole additionally have `sorryAx`. Scanned for forbidden
   declarations and implementation attributes: none. There is exactly one named
   theorem with `sorry`, no partial proof holes and no holed definitions. Pass as
   a decomposition, not as an axiom-free proof of the original item.
3. Rejected the original core as an equivalent restatement. The replacement lower
   theorem concerns only the bottom-edge identification with the derived unit;
   the independent resolution part is actually proved. Checked n=0, zero objects,
   zero additive functors, and identity F: the same unit/inclusion comparison applies,
   or both sides vanish. G is not required to be left exact. The proved transport
   uses hphi exactly in degree zero and works for any I and J, including identity
   and zero resolutions; its Lean proof needs neither left exactness nor Grothendieck
   assumptions. Read the truncation isomorphism's H^0 normalization in Plus.lean
   and the existing unit homology comparison. Searches with new wording through
   Lean Finder/Loogle/grep and rg found no duplicate. The lower hole has a full
   docstring proof, a matching node and cited source. Pass.
4. The original route's two real parts are now separate: the bottom-interval
   identification and the augmented resolution transport. The second part is proved
   using the existing derived unit, rather than split off again. Every retained
   import supplies signature notions or the proof's required lemmas; no unrelated
   import was added. All retired direct proof dependencies are listed above, with
   their continuing transitive use distinguished from pruning. Read
   `dag/units/sk-thm-curveestimate.json`: its realized statement remains
   `thm-sc-proper-cohomology`, with no realized steps bypassed. Pass.
5. Updated the parent node's proof, proof_deps and proof_origin to match the Lean
   proof. Both new nodes carry self-contained statements, source, natural-language
   proof steps, the exact union of step uses, three search kinds (LeanSearch explicitly
   unavailable), provenance, chapter/unit, and verbatim Lean signatures. Existing
   statement/stmt_deps and the unit's realized record remain unchanged. Pass.

Changes by this second reading: removed the equivalent restatement and its node;
wrote and proved the resolution-unit augmentation theorem; stated the genuinely
smaller bottom-edge/unit lemma; replaced the parent's proof with their functorial
combination; corrected its DAG proof metadata and the report's hole accounting.
