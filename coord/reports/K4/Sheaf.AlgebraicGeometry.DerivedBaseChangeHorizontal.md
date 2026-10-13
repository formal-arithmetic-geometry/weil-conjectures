## What changed

Added `DerivedBaseChangeHorizontalMate.lean`, containing the intermediate mate identity
used by the horizontal pasting theorem. The target module imports it and closes its
remaining proof by rewriting with the mate identity and cancelling the canonical
composition isomorphism.

## Proved and sorry left

`AlgebraicGeometry.schemeDerivedBaseChange_horizontal` is proved. The intermediate
`AlgebraicGeometry.schemeDerivedBaseChange_horizontal_mate` remains a named sorry,
with node `new-lem-pc-derived-base-change-horizontal-mate`.

## No longer needed

None. `RelativeMVMaps` remains needed by both declarations.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan omits the explicit intermediate mate identity needed to expose the
canonical relative direct-image composition comparison. No existing theorem in the
library or Mathlib states this identity.

## New nodes

`new-lem-pc-derived-base-change-horizontal-mate` records the intermediate mate
calculation and its source proof plan.

## Second reading by K4

1. **Visible declarations and statements.** Compared the delivered target module with the repository version. The theorem signature of `schemeDerivedBaseChange_horizontal` is byte-for-byte unchanged; the only existing-module changes are a proof-only import and proof body. The added mate module introduces the declaration recorded by its new node.

2. **Compilation and proof hygiene.** Compiled both sandbox modules with `lcompile.py --all`; both pass with no errors. The only remaining `sorry` is the named theorem `schemeDerivedBaseChange_horizontal_mate`, exactly the split-off node. There are no axioms, unsafe declarations, hollow definitions, or forbidden implementation directives. The target proof uses the mate theorem, reassociates, and closes by simp.

3. **New statement audit.** Checked the mate statement against the target's hypotheses and the definitions in `RelativeMVMaps`; it is the strict intermediate equality needed before postcomposition by the target comparison isomorphism. Its docstring gives the mate, naturality, triangle, and coherence argument, and its node records the source, dependencies, and three Mathlib searches. No duplicate declaration was found in the library or Mathlib.

4. **Pruning and dependencies.** The target's public dependency on `RelativeMVMaps` remains required by its statement. The mate module imports that same public dependency; the target imports the mate module privately because only its proof uses the intermediate theorem. No old proof dependency can be removed, and no unused import was introduced.

5. **DAG and unit route.** The target node's proof and `proof_deps` now name the mate node, and the mate node's Lean statement matches its JSON record. The unit `sk-thm-picard-semicon` route is preserved: the intermediate mate calculation feeds the horizontal pasting theorem and does not bypass the unit's realized steps.

Changed during second reading: repaired only node search metadata and this report section; no Lean statement or proof was altered.
