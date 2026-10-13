## What changed
Added fixed-index helper modules for indices 0 and 3. The target theorem now splits its disjunction and applies those helpers.

## Proved and sorry left
The target theorem `perfect_hom_mayerVietoris_geometric_columns_even` is proved by the two fixed-index helper theorems. The helper theorem declarations retain one `sorry` each: `perfect_hom_mayerVietoris_geometric_columns_even_zero` and `perfect_hom_mayerVietoris_geometric_columns_even_three`, recorded in their new nodes.

## No longer needed
No imports or existing nodes were removed.

## Where the brief, the DAG or earlier work was wrong
The planned full geometric argument is not available as a reusable declaration, so the proof was decomposed into its two fixed-index endpoint statements.

## New nodes
`lem-pc-perfect-hom-mayer-vietoris-geometric-columns-even-zero` and `lem-pc-perfect-hom-mayer-vietoris-geometric-columns-even-three` are fixed-index strict specializations used by the target proof.

## Second reading by M2

1. Compared the delivered main module with the repository version. The target signature is unchanged; only proof imports and proof body differ.
2. Compiled all three delivered modules successfully with `lcompile.py`; the two helper declarations intentionally remain named `sorry` holes and no forbidden declarations were found.
3. Checked the helper statements against their fixed-index specializations and verified the parent proof applies them only after reducing `Fin` indices. The helpers are strictly narrower but remain open obligations.
4. The proof follows the fixed-index route recorded in the DAG and preserves the unit's outer-column route; no imports or existing nodes were pruned.
5. Updated both helper node `lean.statement` fields to the exact Lean signatures and verified the DAG proof dependencies match the source imports.

The helper modules and their nodes remain the only split-off obligations; no target statement or definition was changed.
