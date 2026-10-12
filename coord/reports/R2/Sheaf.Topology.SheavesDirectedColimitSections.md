## What changed
Reduced the target theorem to three named auxiliary theorems: construction of the canonical maps, compact-open injectivity/eventual equality, and finite-cover surjectivity. The target proof now combines these three statements in Lean.

## Proved and sorry left
`TopCat.sheaves_directedColimit_sections` is proved by combining the three auxiliary declarations. The auxiliary declarations `TopCat.directedColimit_sections_map`, `TopCat.directedColimit_sections_injective`, and `TopCat.directedColimit_sections_surjective` remain `sorry`, each with a DAG node.

## No longer needed
No imports were removed. No stated dependencies are pruned.

## Where the brief, the DAG or earlier work was wrong
The original four-step proof is mathematically sound but too large for this worker's time; it was split into three strictly smaller named stages.

## New nodes
Added `aux-directed-colimit-map`, `aux-directed-colimit-injective`, and `aux-directed-colimit-surjective`.

## Earlier second reading (a previous round; superseded)
The reduction compiles and preserves the target signature; the three auxiliary statements are strict subarguments of the four-step Stacks proof and are ready for subsequent workers.

## Second reading by R2

1. Compared the delivered module with the repository version. The target signature and all
   pre-existing declarations are unchanged; only the target proof and three named auxiliary
   declarations were added.
2. Compiled the module with `lcompile.py --all`. It compiles cleanly after shortening the three
   overlong documentation lines. The target has no `sorry`; the three auxiliary theorems are the
   documented split-off sorries. No prohibited declarations or hollow definitions occur.
3. Checked the reduction: the target obtains the canonical maps and applies the separate
   injectivity and surjectivity statements, so each split theorem is a strict subargument rather
   than a restatement of the target. Their statements preserve the hypotheses and conclusions
   used by the target.
4. Checked pruning and imports. The existing imports are both used (the sheaf API supplies the
   colimits and the local sheafification module supplies the surrounding development), so no
   import or proof dependency can be removed. The unit route remains the map, compact-open
   injectivity, and finite-cover surjectivity sequence.
5. Checked the DAG entries against the declarations and report. Each split theorem has a matching
   node, source, blueprint, and `lean` record; no new statement is claimed to be a Mathlib
   theorem. The target node's proof is represented by the three auxiliary uses.

Changed in this second reading: shortened documentation lines to satisfy the 100-character
style check and added this review record. No mathematical statement or proof dependency changed.
