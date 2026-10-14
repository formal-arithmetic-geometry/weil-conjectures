## What changed
Split the conjunction into two named intermediate theorems and combined them in the target theorem.

## Proved and sorry left
Closed: `AlgebraicGeometry.Scheme.Modules.tensorGradedAction_projection` (one of one original holes), by combining its strict conjuncts.

Added/open: `AlgebraicGeometry.Scheme.Modules.tensorGradedAction_projection_first` (node `lem-sc-square-zero-tensor-graded-action-projection-first`) and `AlgebraicGeometry.Scheme.Modules.tensorGradedAction_projection_second` (node `lem-sc-square-zero-tensor-graded-action-projection-second`).

This is a decomposition, not a complete proof: one hole closed, two added, net minus one hole closed. Neither conjunct was discharged.

## No longer needed
No proof-dependency module was pruned. The parent now delegates the six original proof dependencies to the child nodes, which retain the same original route. Unchanged dependency source copies and one stale presentation copy were excluded from the delivery.

## Where the brief, the DAG or earlier work was wrong
The original proof plan requires substantial local sheaf and cohomology naturality arguments; these were isolated as the two strict conjunct statements so the parent theorem has a complete Lean proof.

## New nodes
`lem-sc-square-zero-tensor-graded-action-projection-first`, `lem-sc-square-zero-tensor-graded-action-projection-second`.

## Second reading by T2

1. I compared the delivered target module with the repository version. The target signature and all existing declarations are unchanged; the only target change is its proof. I found and removed a stale copied `SquareZeroTensorGradedPresentation.lean` that would have reverted an upstream definition and was not needed by this item.

2. The parent theorem compiles. Its proof is a genuine conjunction construction using the two strict conjunct declarations. The two child declarations remain named `sorry`s with source and proof narratives; they are not definitions or axioms. Axiom probing shows only the intended `sorryAx` from those open child statements, together with the standard axioms.

3. The two split statements are true, each is exactly one conjunct of the unchanged target, and neither adds hypotheses or weakens the conclusion. Their nodes now describe the corresponding single equation and no longer claim the circular parent theorem as their proof. Searches found no existing Mathlib or library duplicate.

4. The parent proof uses the product-projection route through the two new conjunct nodes. The unit has no proof steps to bypass, so the route is preserved. No imports used only by the stale presentation copy are delivered.

5. I updated the child node `proof`, `proof_deps`, `proof_origin`, Lean statements, and search records to agree with the code. The parent node now records the strict conjunct decomposition and depends on the two children.

Changed: repaired child docstrings and DAG metadata, removed stale dependency copies from the delivery, retained the parent conjunction proof, and added this second reading.
