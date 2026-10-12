## What changed
Added complete composition of the universal property from separate existence and uniqueness helper theorems. The helpers are explicitly named public statements with documented proof obligations.

## Proved and sorry left
The target `changeOfRings_tensor_balancing_universal` is proved by applying the existence and uniqueness clauses. Sorry remains in `changeOfRings_tensor_balancing_universal_exists` and `changeOfRings_tensor_balancing_universal_unique`, each recorded as a new DAG node.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The original target proof requires substantial sheafification and tensor-generation arguments; these were split into independent existence and uniqueness obligations so the target proof itself is complete.

## New nodes
`aux-lem-weil-pbc-change-of-rings-tensor-balancing-universal-exists` and `aux-lem-weil-pbc-change-of-rings-tensor-balancing-universal-unique`.

## Earlier second reading (a previous round; superseded)
The target compiles and its proof invokes the two strictly smaller existence and uniqueness statements. The helper statements are true clauses of the target and preserve the unit route.

## Second reading by M2

1. The target signature is byte-for-byte unchanged against `sheaf-dag`; the delivered proof only composes the two clauses. Verdict: pass.
2. All delivered modules compile with `lcompile.py`; the target has no direct `sorry`, while the existence clause remains the only open theorem. No forbidden declarations or hollow definitions were added. Verdict: pass.
3. The existence and uniqueness clauses are genuine component statements of the universal property. The uniqueness proof was checked directly by sheafification extensionality and tensor induction; the existence clause remains explicitly sourced and documented. Verdict: pass with one split theorem left open.
4. The proof uses the existing sheafification and tensor imports and adds no unnecessary public imports. The unit route is retained through the balancing universal-property node. Verdict: pass.
5. DAG records now match the three module declarations, with the parent proof depending on the two component nodes. Verdict: pass.

Changed the delivery by moving the component declarations into dedicated modules, proving the uniqueness component, updating the parent DAG proof route, and recording the remaining existence hole and dependency modules.

## Dependency modules

`Sheaf.AlgebraicGeometry.ChangeOfRingsTensorBalancingExists` contains the documented existence component and its node; `Sheaf.AlgebraicGeometry.ChangeOfRingsTensorBalancingUnique` contains the proved uniqueness component and its node.
