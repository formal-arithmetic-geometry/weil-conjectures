## What changed

The target theorem `AlgebraicGeometry.relativeMV_direct_image_rows` is now proved by composing two strictly smaller named intermediate theorems. The target imports `RelativeMVDirectImageRowsPreoverlap` and `RelativeMVDirectImageRowsOverlapMate`; its public statement and all existing imports needed by that statement are unchanged.

`relativeMV_direct_image_rows_preoverlap` records the resolved rows, vertex comparisons, short exactness, the global and middle mate identities, and the overlap mate before cancellation with `e₃'`. `relativeMV_direct_image_rows_overlap_mate` is the proved cancellation step. The target proof itself is complete Lean composition.

The target node proof and proof dependencies were updated to match the two declarations. Two new DAG nodes and two new Lean modules were added.

## Proved and sorry left

Closed the target hole `AlgebraicGeometry.relativeMV_direct_image_rows` (node `lem-pc-relative-mv-direct-image-rows`) by applying the two intermediate declarations and assembling their conjunctions.

The following strictly smaller obligation remains as a named `sorry`:

- `AlgebraicGeometry.relativeMV_direct_image_rows_preoverlap` (node `lem-pc-relative-mv-direct-image-rows-preoverlap`), constructing the rows and all three mate data before the final inverse cancellation.

The declaration `AlgebraicGeometry.relativeMV_direct_image_rows_overlap_mate` (node `lem-pc-relative-mv-direct-image-rows-overlap-mate`) is proved by a real `congrArg` and categorical cancellation argument.

No definitions contain `sorry`; no axiom or unsafe declaration was added.

## No longer needed

The target and the pre-overlap helper no longer import the original private
proof modules directly: `RingedSiteKInjectiveResolutions`,
`KInjectiveMayerVietorisPresentation`,
`DerivedMayerVietorisUnderivedOpenCounitSquare`,
`RingedSpaceDirectImageKInjectiveAcyclic`,
`DerivedPullbackConeSquareTransposition`,
`ConeDiagramFullSESPresentation`, and `HomotopySquareRectification`.
The parent `RelativeMVDirectImageHomotopyComparison` is also deliberately not
imported: it depends on this target and would create an import cycle.
The two split declarations are the only interfaces used by the target proof.
No blueprint unit route is bypassed, and no existing library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof bundled strict row construction, rectification, and the
overlap counit calculation into one declaration. Those are independent
subclaims with different interfaces, so the delivery records them as two
intermediate nodes. The target statement is unchanged.

## New nodes

`lem-pc-relative-mv-direct-image-rows-preoverlap` in `Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsPreoverlap` is the strict-row and pre-cancellation mate subclaim. Its source is the resolved Mayer--Vietoris construction in Stacks Tags 08BV, 08HZ, 08FE and 08HY.

`lem-pc-relative-mv-direct-image-rows-overlap-mate` in `Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsOverlapMate` is the inverse-cancellation component, proved from the pre-cancellation equation and the target vertex isomorphism.

## Earlier second reading (a previous round; superseded)

The target proof compiles from the two named declarations. The pre-overlap
node contains the resolved-row construction and the pre-cancellation overlap
mate; the overlap node is a strictly simpler cancellation lemma whose proof is
complete. The target statement and the unit route are unchanged.

## Second reading by W4

1. **Signatures and accidental changes.** Compared the delivered target with
   `lean/Sheaf/AlgebraicGeometry/RelativeMVDirectImageRows.lean` in the
   repository. The target theorem signature is byte-for-byte unchanged. The
   two additional modules are new; no held module was adapted.

2. **Proof and axioms.** Compiled all three modules with `lcompile.py`. The
   target and the cancellation theorem contain complete proofs. The only
   remaining `sorry` is the named theorem
   `AlgebraicGeometry.relativeMV_direct_image_rows_preoverlap`; it is listed
   in its node and has a source and proof sketch. No definition contains a
   `sorry`, and no forbidden declaration was added.

3. **Statements and split nodes.** Checked the two split statements against
   their uses and the categorical cancellation calculation. The preoverlap
   theorem is the strict-row construction needed by the target. The overlap
   theorem was pruned to the exact cancellation input (`e₃`, `e₃'`, and its
   pre-cancellation equation), so it does not assume unrelated row data.
   The node statements and Lean declarations agree.

4. **Pruning and imports.** Removed the old private proof imports from the
   target. The overlap module now imports only the public modules needed by its
   statement; it has no proof dependency on the preoverlap theorem because it
   is a generic cancellation lemma. The target still uses both split
   declarations, and no unit route is bypassed.

5. **DAG and route.** Updated the overlap node's proof, proof dependencies,
   proof origin, and verbatim Lean statement to match the repaired proof. The
   preoverlap node remains the sole open obligation; its source, declaration,
   and dependency list agree with the delivered module.

**Changes made during second reading.** Removed redundant arguments from
`relativeMV_direct_image_rows_overlap_mate`, changed its imports to the direct
public statement dependencies, updated its DAG node accordingly, and recorded
this section.
