## What changed

The target proof now constructs the boundary data through the named intermediate theorem `mvBoundary_data` and closes the target by applying the named compatibility theorem `mvBoundary_equation`. Added module `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundaryData` and node `lem-pc-rf-mv-base-change-connecting-square-data`; both lower theorems are explicit split obligations with documented sources.

## Proved and sorry left

`AlgebraicGeometry.derivedBaseChange_mayerVietoris_connectingSquare` is proved by real Lean composition from the two named intermediate statements. `AlgebraicGeometry.mvBoundary_data` remains `sorry`, node `lem-pc-rf-mv-base-change-connecting-square-data`. `AlgebraicGeometry.mvBoundary_equation` remains `sorry`, node `lem-pc-rf-mv-base-change-connecting-square-equation` (the compatibility calculation is a strictly separate chain-level obligation).

## No longer needed

The rejected unconstrained helper from the earlier attempt is not imported or delivered. No original proof dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stated an equation for arbitrary independently chosen boundaries and shift structures; that statement is false. The delivered equation is attached to the canonical distinguished-boundary data and is used only after `mvBoundary_data` supplies that data.

## New nodes

`lem-pc-rf-mv-base-change-connecting-square-data`: existence and distinguishedness data used by the target proof.  The compatibility equation is split as `lem-pc-rf-mv-base-change-connecting-square-equation` in the same data module; both are lower obligations and neither restates the full target.

## Second reading by K3

1. Compared both delivered modules with the repository version. The target signature and all existing declaration signatures are unchanged; only the target proof, a proof-only import, and the two new declarations were added.
2. Compiled the modules with `lcompile.py --all`; both compile successfully with no warnings, and the delivered theorems contain no forbidden declarations or hollow definitions. The two remaining `sorry`s are whole proofs of named public theorems and each has a corresponding node.
3. Checked the split statements against the target and small degenerate-cover cases. `mvBoundary_data` supplies exactly the existential data and distinguishedness conjuncts; `mvBoundary_equation` supplies only the final equality for that supplied canonical data. They are strictly smaller than the target and have documented sources and DAG records.
4. Checked the proof route and imports. The target now applies the data construction and then the compatibility equation; the unit route through Mayer--Vietoris functoriality and derived direct-image composition is retained. No unused original import was identified.
5. Checked that node `proof`, `proof_deps`, and `proof_origin` match the Lean proof, and that both new nodes carry blueprint references, sources, searches, and declarations. The prior unconstrained-boundary equation was discarded as false; the delivered equation is restricted to the canonical distinguished data.

Changed the overlong line in the data module, added the missing equation node, and updated the item's proof metadata to cite both split nodes.
