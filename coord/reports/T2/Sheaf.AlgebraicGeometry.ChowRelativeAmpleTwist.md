## What changed
Split `chow_relative_ample_twist` into two strictly smaller public component theorems, imported them, and proved the parent by pairing their results. The component proofs remain documented `sorry`s for parallel workers.

## Proved and sorry left
The parent `chow_relative_ample_twist` is proved. `chow_relative_ample_twist_iso` and `chow_relative_ample_twist_properties` remain as named intermediate obligations, each with its own DAG node.

## No longer needed
None; the original proof imports are retained as the stated route dependencies.

## Where the brief, the DAG or earlier work was wrong
The parent proof is too large to close directly in this item; decomposition into its two conjunction components is the strict reduction used here.

## New nodes
`lem-pc-chow-relative-ample-twist-iso` and `lem-pc-chow-relative-ample-twist-properties`.

## Earlier second reading (a previous round; superseded)
The parent proof is unchanged in signature and combines exactly the two strict conjuncts. The new component statements are strictly smaller and match the corresponding portions of the parent conclusion.

## Second reading by T2
1. Compared the delivered parent module with the repository version. The theorem signature is byte-for-byte unchanged; only its proof and proof-only imports changed. Verdict: pass.
2. Compiled all five sandbox modules with `lcompile.py --all`; there are no errors. The only remaining `sorry`s are the two named component theorems, and neither definition contains a `sorry`. Verdict: pass for the parent proof, with the two documented split obligations open.
3. Read both split statements and their DAG nodes. Each is a strict conjunct of the parent conclusion, with the same hypotheses and no weakened conclusion; their source and proof descriptions point to Stacks Tag 02O5. Verdict: pass as a decomposition, pending independent proofs of the components.
4. The parent proof takes the shortest available route by pairing the two component declarations. The prior geometric and affine-invertibility imports are no longer used and were removed. Verdict: pass; the unit route is represented by the component nodes.
5. The DAG `lean` records match the declarations and the parent node now records the two component uses through the Lean imports. Verdict: pass.

Changed the parent imports by removing `ChowRelativeAmpleGeometric` and `ProjectiveAmpleInvertible`, which are unnecessary after decomposition, and added this second-reading record. No statement or definition was changed.
