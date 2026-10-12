## What changed

Removed the private declaration `lift_arrow_above_stage`, whose statement was
already present word for word in `Sheaf.CategoryTheory.ColimitSiteCoveringAxiomsHasPullbacks`
and was rejected by `import_prune_check.py`. Its short lifting argument is now
performed inline in the main proof immediately before the common-target
refinement. The target theorem signature, imports, and visibility are unchanged.

## Proved and sorry left

`CategoryTheory.filtered_colimit_iso_presieve_representation` remains fully
proved, with no `sorry` left in this item. No new holes were added.

## No longer needed

The duplicate private declaration `lift_arrow_above_stage` and its separate
module-level statement are no longer needed; the same construction is local to
the target proof. No other imports or DAG dependencies were removed.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery introduced a module-level private theorem whose statement
was already present in the pullbacks module. Although the existing declaration
is private and cannot be referenced by its source name from another module, the
duplicate declaration is unnecessary: inlining its proof preserves the planned
argument while satisfying the import-pruning check.

## Second reading by G3

1. Compared the delivered module with the repository version. The public theorem
   signature, declarations, and visibility are unchanged; only its proof and the
   proof-only `Mathlib.CategoryTheory.Limits.Types.Filtered` import differ.
2. Compiled the module with `lcompile.py`; it is clean and contains no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses only
   filtered-colimit equality and joint-surjectivity APIs, and the private helpers
   are ordinary proved lemmas.
3. The theorem statement is unchanged from node
   `lem-weil-pbc-filtered-colimit-iso-presieve-representation`; no split-off
   statements or new holes were added, and the singleton stage covering is exactly
   the `HasIsos` conclusion required by the node.
4. The proof follows the unit route: representatives for an arrow and its inverse,
   common endpoint refinement, refinement of both inverse equations, and a final
   stage isomorphism. No unit step is bypassed. The only added import is used by the
   filtered-colimit equality criterion.
5. The DAG node's proof and dependency metadata match the proof: it uses the
   filtered-colimit sets elementwise lemma and the category-arrow functor; no
   dependency was removed or invented.

Changed only the proof by retaining the inline lifting argument and adding the
proof-only filtered-colimit import. No declarations or node files required repair.
