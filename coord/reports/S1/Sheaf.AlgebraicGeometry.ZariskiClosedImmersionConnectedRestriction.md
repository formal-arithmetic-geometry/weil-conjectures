## What changed

Replaced the target theorem's original `sorry` with a complete application of a named universe-transport intermediate theorem. The setup establishes the spectral instances, closed image, and connected point-closure intersections. The intermediate theorem records the ULift/order-isomorphism transport from `TopCat.spectral_closed_restriction` to the Type `(u+1)` Zariski inverse-image unit.

## Proved and sorry left

`AlgebraicGeometry.zariski_closed_immersion_connected_restriction` is proved. The intermediate declaration `AlgebraicGeometry.zariski_restriction_universe_transport` remains `sorry`; it is the strict universe-transport step split into its own DAG node.

## No longer needed

No imports or existing nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

The direct application of `TopCat.spectral_closed_restriction` has a universe mismatch: it produces a sheaf in `Type u`, while the target uses `Type (u+1)`. The ULift transport must therefore be isolated as an intermediate theorem.

## New nodes

`lem-weil-pbc-zariski-restriction-universe-transport` records the remaining transport proof.

## Second reading by S1

1. Compared the delivered module with the repository version. The target theorem signature is unchanged; the added transport theorem is now pointwise in the sheaf rather than a restatement of the target's universal quantifier.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. The only remaining `sorry` is the named universe-transport theorem, and there are no forbidden declarations.
3. Checked the new pointwise transport statement against the ULift transport step and updated its node, proof dependencies, and proof description. It is strictly weaker than the item and is used once for each sheaf.
4. The route keeps the spectral closed restriction unit and the connectedness setup; no imports or old dependencies were pruned.
5. The DAG node and Lean declaration agree after changing the node to the pointwise statement.

Changed the split theorem from a universal restatement to a pointwise transport lemma, removed linter-producing `letI`s, and updated the node and this report.
