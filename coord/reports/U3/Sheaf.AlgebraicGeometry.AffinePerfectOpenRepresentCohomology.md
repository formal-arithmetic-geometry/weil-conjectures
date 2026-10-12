## What changed

Split the original proof into two named intermediate public theorems, one for the finite Koszul structural conjunction and one for the inverse augmentation and colimit representability conjunction. The original theorem now combines these two statements by a complete constructor proof. Added proof-only imports of the two intermediate modules.

## Proved and sorry left

The original theorem `AlgebraicGeometry.affine_perfect_open_represent_cohomology` is reduced by a real conjunction proof. Two strictly smaller intermediate theorems remain as named `sorry`s: `AlgebraicGeometry.affine_perfect_open_represent_cohomology_core` and `AlgebraicGeometry.affine_perfect_open_represent_cohomology_colimit`, with corresponding nodes.

## No longer needed

No imports or planned proof dependencies were pruned; all original dependencies remain available to the intermediate statements.

## Where the brief, the DAG or earlier work was wrong

The original proof plan was too coarse for the available time. The argument naturally decomposes into the structural clauses and the representability/colimit clauses; both intermediate statements are strict parts of the target and compile independently.

## New nodes

`lem-sc-affine-perfect-open-represent-cohomology-core` records the first three structural clauses.

`lem-sc-affine-perfect-open-represent-cohomology-colimit` records the final representability and colimit clauses.

## Earlier second reading (a previous round; superseded)

Pending independent second reading; the two intermediate statements are strict sub-conjunctions of the target and the combining proof compiles.

## Second reading by U3

1. **Visible declarations and statements.** Compared both delivered versions against the repository with `diff`; the existing target declaration and all its hypotheses and conclusions are byte-for-byte unchanged. The two added declarations are strict conjunctions of the target clauses and do not alter any existing definition.

2. **Compilation and proof audit.** Compiled all three sandbox modules with `lcompile.py --all`; compilation succeeds. The target theorem has a complete constructor proof. The only remaining `sorry`s are the two explicitly named intermediate theorems `affine_perfect_open_represent_cohomology_core` and `affine_perfect_open_represent_cohomology_colimit`, each documented and represented by a node. No definitions contain `sorry`, and no forbidden `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declaration was added.

3. **Truth and strength of split statements.** Checked the core statement against the first three target conjuncts and the colimit statement against the final inverse-augmentation and cocone conjuncts. Each is a strict part of the original target, with the same parameters and typeclass assumptions, and is needed directly by the combining proof. The source is the cited Stacks Tags 08CX, 08DC, and 08DD argument; no matching Mathlib or upstream declaration was found.

4. **Pruning and route.** The target's proof follows the stated unit route: it invokes the structural Koszul theorem and the representability/colimit theorem, then assembles their conjunctions. All proof-only imports remain available to the split statements, and no import or planned dependency became unused in this decomposition; consequently there are no pruning changes.

5. **Nodes and unit metadata.** Verified that both new node files carry matching Lean module/declaration records, `split` status, source, proof, proof dependencies, blueprint, chapter, and unit metadata. The unit `sk-thm-picard-duality` remains realized by the original target node; the new nodes only decompose its proof below the unit level.

Changed only this report by adding the required independent second-reading record. No Lean source or DAG node was changed during the reading.
