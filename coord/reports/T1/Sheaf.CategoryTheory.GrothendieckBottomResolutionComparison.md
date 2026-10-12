## What changed

Removed the three duplicate top-level declarations rejected by the import-prune
checker. Their existing proof terms are now local `have` declarations inside
the composite transport proof, so the target has no duplicate library
declarations. The remaining private transport proofs and target proof are
unchanged apart from those local call sites.

The returned delivery's split-off augmentation module remains imported and is
still the only unresolved intermediate statement.

## Proved and sorry left

Closed `CategoryTheory.grothendieckBottomEdgeMap_eq_resolution` with the
local comparison proof terms and the existing transport proofs.
The target module contains no `sorry`. This is a decomposition: one upper hole
is closed and one strictly smaller augmentation hole is added, for net zero
holes closed. The target still depends on `sorryAx` through that augmentation.

The one split-off hole remains:
`CategoryTheory.grothendieckBottomEdge_augmentation` in
`Sheaf.CategoryTheory.GrothendieckBottomAugmentation`.

## No longer needed

The three duplicate private helper declarations and their proofs are removed.
The direct proof dependency
`lem-pc-canonical-resolution-composite-unit-comparison` is no longer used: its
public theorem assumes Grothendieck abelian C, which the unchanged item does
not assume. The necessary transport is proved locally without that assumption.
`lem-sp-derived-well-defined` is also no longer a direct dependency of the
item; it remains a dependency of the augmentation node and an upstream
foundation. No formerly imported module is removed and no module is claimed
as pruned.

## Where the brief, the DAG or earlier work was wrong

The prior delivery duplicated three declarations already present in
`CanonicalResolutionCompositeUnitComparison`; the import-prune checker
correctly rejected those duplicates. This repair keeps the same proof route
but scopes those proof terms locally inside the transport theorem.

## New nodes

The existing split-off node lem-sc-grothendieck-bottom-augmentation remains the one new node delivered by the earlier split.

## Earlier second reading (a previous round; superseded)

Recompiled the item and its split-off module with lcompile.py. Confirmed that the three duplicate top-level declarations are gone and that the target still has no sorry. Confirmed no adapted external module is included.

## Second reading by T1

1. **Interface: pass.** Diffed both delivered modules against the repository
   (the augmentation module is new). The existing public theorem's signature
   is byte-for-byte identical, including arbitrary abelian C, hFG, hφ and n.
   No existing definition or public import is changed. No forced adaptation
   or statement change is delivered.
2. **Proof: pass as a decomposition.** Compiled the two modules in import order
   with lcompile.py. The only delivered sorry is the named public augmentation
   theorem. No prohibited declarations or hollow definitions occur. A scratch
   copy with #print axioms showed only propext, Classical.choice and Quot.sound
   for both private transport lemmas; the target and augmentation additionally
   have sorryAx. The canonical comparison data is constructed from explicit
   augmentations and map/extension isomorphisms, not arbitrary existence data.
3. **Split: pass.** Read the augmentation statement, docstring and node. It
   isolates the bottom truncation inclusion before the derived-composite and
   G-resolution identifications; it drops both hFG and left exactness of G.
   It is therefore a strictly smaller part of the argument, not the original
   resolution formula renamed. Checked degree zero (no incoming differential),
   zero objects and zero functors, and arbitrary augmentation-preserving φ:
   cancellation of the J augmentation determines its derived morphism.
   Fresh leanfinder and loogle searches for truncation-inclusion naturality
   found generic CochainComplex truncation lemmas, not this transported edge
   identity. rg across both Lean roots and Mathlib likewise found no duplicate.
   Closing this truncation/derived-unit identification requires more than a
   few-minute proof; the sourced hole remains explicit.
4. **Route/imports: pass after report repair.** The raw edge is reduced to the
   augmentation, the G-unit naturality calculation, and the composite-unit
   calculation. CanonicalResolutionHomologyComparison supplies the already
   proved ordinary resolution calculation. Both added imports of the item are
   proof-only; both public imports of the new module are needed in its type.
   The composite-unit public theorem cannot be applied to arbitrary abelian C;
   the local proofs generalize its private ingredients without new holes.
   The unit sk-thm-curveestimate realized statement is thm-sc-proper-cohomology,
   with no realized steps here, and its route is unchanged. No module is pruned.
5. **DAG: pass after repair.** Checked source, statement, chapter/unit,
   blueprint provenance, searches and Lean record of the new node. The item's
   proof_deps now equals the union of uses in its three proof steps, removing
   the stale composite-unit dependency. Restored the existing Lean record's
   statement from the repository: the earlier sandbox record contained literal
   Unicode escape text instead of the declaration characters. The proof_origin
   now describes the actual local generalization and augmentation reduction.

Second reading changed the DAG dependency list, proof_origin and corrupted
Lean statement metadata; completed the pruning report and explicitly recorded
one closed hole, one added hole and net zero. No Lean proof was rewritten.
