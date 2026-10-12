## What changed

Split the target proof into two named intermediate component theorems, one for degrees above one and one for degree-two pullbacks. The target module now combines these component results. Added proof-only imports for both component modules.

## Proved and sorry left

`AlgebraicGeometry.IsCurve.dense_open_high_cohomology` is proved by pairing the two component theorems. The new component declarations `dense_open_high_cohomology_high` and `dense_open_high_cohomology_pullback` retain `sorry`, each with a dedicated DAG node.

## No longer needed

None beyond the target's original imports; all original geometric proof dependencies remain available for the split component arguments.

## Where the brief, the DAG or earlier work was wrong

The original target proof plan requires substantial open-closed geometry and long-exact-sequence glue. That glue was split into two independently stated component results so the target reduction compiles cleanly.

## New nodes

`lem-pbc-s2-dense-open-high-cohomology-high` records the higher-degree component. `lem-pbc-s2-dense-open-cohomology-pullback` records the degree-two pullback component.

## Earlier second reading (a previous round; superseded)

The component statements are strict parts of the target and the target combines them without changing its signature. Each remaining sorry has a matching node.

## Second reading by Y2

1. The delivered target module was diffed against the repository version. Its theorem signature is byte-for-byte unchanged; only proof-only imports and the proof body were added. The two component declarations are new, documented split statements, and the target still has exactly the original hypotheses and conclusion.
2. All three delivered modules compile with `lcompile.py --all`. The only remaining `sorry`s are the two named component theorems, each with a matching DAG node; there are no hollow definitions, axioms, unsafe declarations, or other forbidden constructs.
3. The component statements are strict projections of the target (higher degrees and degree-two pullbacks), hence true and exactly sufficient for the conjunction. Their DAG proof plans now reduce to the closed-complement, exact-sequence, finite-direct-image, and zero-dimensional-vanishing dependencies rather than citing the target itself.
4. The target proof follows the shortest available reduction in this module: it unfolds the `let` and pairs the two component results. The imports needed by the target and components are retained; no unused import was found.
5. The DAG proof, proof dependencies, and proof origins agree with the Lean declarations. The unit route is preserved: the target node remains the realized node for the dense-open comparison step, with the component nodes supplying its two conclusions.

I changed the two new node proof plans to remove their circular dependency on the target and added this second-reading record. No Lean statements or definitions were changed.
