## What changed
Added `InjectiveSplitTowerExtension` with the compatible lifting intermediate theorem (left as a named proof obligation), and proved `injective_of_injective_split_tower` by constructing `Injective` and applying that extension theorem.

## Proved and sorry left
Closed `injective_of_injective_split_tower`. The only remaining sorry is `injective_split_tower_extension`, with node `lem-pc-injective-split-tower-extension`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The planned compatible lifting argument is substantial, so it was isolated as a strictly lower-level extension theorem; the target proof is the genuine constructor application.

## Earlier second reading (a previous round; superseded)
The target proof preserves the exact statement and reduces it to the explicit compatible extension obligation. The new statement is strictly the one-monomorphism lifting step used by the target.

## New nodes
`lem-pc-injective-split-tower-extension` in `dag/nodes/sec-picard-framework/lem-pc-injective-split-tower-extension.json`.

## Second reading by Q2

1. Compared the delivered `InjectiveSplitTower.lean` against the repository version. The existing theorem signature is byte-for-byte unchanged; only its proof and a proof-only import were added. The extension module is a new declaration and is recorded by the accompanying node.
2. Compiled both modules with `lcompile.py --all`; they compile cleanly. The target theorem has no `sorry`; the named extension theorem is the sole remaining sorry. No forbidden declarations or sorry in definitions were found.
3. Checked the extension statement against the compatible lifting argument in Stacks Tag 07KW. It is a direct one-monomorphism lifting statement with the same tower, levelwise injectivity, split transition, and compatibility conclusion. The new node supplies its source, proof plan, and Lean declaration; no existing Mathlib or Sheaf declaration states it.
4. The target proof uses the extension theorem exactly to construct the required witness for `Injective`; the unit route through split-tower injectivity is retained. No old proof dependency or import became unnecessary.
5. The remaining extension obligation is a strictly lower-level decomposition of the target proof (level-by-level extension and kernel correction), rather than a restatement of the target. Its node and Lean declaration agree, and the unit's realized route remains unchanged.

Changed during second reading: added this review record only; no theorem statements or definitions were altered.
