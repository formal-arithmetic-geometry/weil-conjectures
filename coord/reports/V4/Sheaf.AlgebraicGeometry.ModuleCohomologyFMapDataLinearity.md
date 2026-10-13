## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMapData_map_linear`
with a proof from the existing
`AlgebraicGeometry.Scheme.Modules.ModuleCohomologyFMapData.map_semilinear`.
Added its proof-only import
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapSemilinear`.
Mathlib's `ModuleCat.semilinearMapAddEquiv` turns that semilinear map into a
morphism to the restriction of scalars. Extensionality proves the required
forgetful-map equality using the lift's pointwise equality.
All existing signatures, visibility, definitions, and public imports are unchanged.
Updated the item's DAG proof, proof_deps, and proof_origin to describe this route.
The item is not a statement or step listed in its unit's realized route; that route is preserved.

The module compiled cleanly through lcompile.py. Search used the prescribed
LeanFinder and Loogle endpoints and ripgrep over the existing library and Mathlib.
Loogle found the exact generic conversion `ModuleCat.semilinearMapAddEquiv`.

## Proved and sorry left

Closed 1 of 1 holes in the item's module:
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMapData_map_linear`
(node `lem-weil-pbc-module-cohomology-fmap-data-linearity`).
No sorry remains in the item's module, and no new holes or modules are added.
The existing dependency
`AlgebraicGeometry.Scheme.Modules.ModuleCohomologyFMapData.map_semilinear`
(node `lem-weil-pbc-module-cohomology-fmap-semilinear-lift`)
is still sorry in the library. This delivery proves the item from that existing
statement; it does not independently prove the resolution-linearity argument.

## No longer needed

No original import is removed and no module is pruned.
The old proof dependency `def-weil-pbc-module-cohomology-fmap` is no longer
used as a direct proof step; it is replaced in `proof_deps` by
`lem-weil-pbc-module-cohomology-fmap-semilinear-lift`. Its module
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMap` remains necessary for the
statement and as a dependency of the semilinear-lift theorem, so its import
is retained. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan did not identify the existing semilinear-lift declaration,
which already states the needed content in a form handled by Mathlib's generic
restriction-of-scalars equivalence. Reusing it avoids duplicating the homology
comparison argument. No mathematical statement or interface correction was needed.

## Second reading by V4

1. Compared the delivered Lean module and DAG node with the repository using
   `diff -u`. The only Lean changes are the plain proof-only semilinear import
   and replacement of the theorem's proof. The existing signature, docstrings,
   visibility, definitions and public import are byte for byte unchanged.
   No change record is needed. Verdict: pass.
2. Compiled the delivered module with the prescribed `lcompile.py`: exit 0,
   no warnings. Read every line: no sorry or forbidden declaration is added,
   and no definition or arbitrary choice of data is introduced. Compiled a
   scratch copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMapData_map_linear`:
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The existing semilinear-lift theorem is unproved, as disclosed above;
   this closes the local hole conditionally on that existing dependency.
   Verdict: pass with the documented upstream hole.
3. No statement or node is split off, and no new hole is introduced.
   Read the existing semilinear theorem and Mathlib's equivalence:
   restriction of scalars turns the semilinear equation into precisely the
   required linearity, retaining the same underlying function. The argument
   works uniformly in degree zero, zero modules, and arbitrary scheme maps;
   it introduces no extra hypothesis. Verdict: pass.
4. Searched the local Sheaf and upstream library for alternative linearity
   and semilinearity declarations and read Mathlib
   `Algebra/Category/ModuleCat/ChangeOfRings.lean`'s
   `ModuleCat.semilinearMapAddEquiv`. The existing generic equivalence gives
   the direct four-line reduction; reconstructing a linear map from the
   scalar-compatibility theorem would repeat its fields. Both imports are
   necessary, and the newly added import is proof-only. Read
   `dag/units/sk-thm-p1.json`: none of its realized statement or step nodes
   is bypassed, and the unit record is unchanged. Corrected the pruning
   report to name the removed direct proof dependency explicitly. No module
   is pruned. Verdict: pass after this report correction.
5. Read the original and delivered node plus the semilinear-lift node.
   Only `proof`, `proof_deps`, and `proof_origin` change. The proof's two
   steps match the Lean: obtain the lift, then bundle it via Mathlib and
   identify the additive morphisms by extensionality. `proof_deps` is the
   union of the steps' node dependencies; the definition node stays in
   `stmt_deps`. No new node fields are required. Verdict: pass.

Second reading changed only this report: completed `## No longer needed`
and recorded these checks. The Lean proof and DAG update needed no repair.
