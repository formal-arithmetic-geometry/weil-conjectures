## What changed
Repaired return X-81ed4: removed the duplicate private declarations
`AlgebraicGeometry.inverse_stalkMap_germ` and
`AlgebraicGeometry.restriction_stalk_smul` from
`Sheaf.AlgebraicGeometry.OpenOrdinaryTensorPureGermCoordinatesCanonical`.
Added a proof-only `import all Sheaf.AlgebraicGeometry.OpenModuleStalkRestrictionComparison`
and used its existing private `AlgebraicGeometry.Scheme.restriction_stalk_smul` in
`open_coordinate_smul`. Lean's `import all` permits this reuse without changing the
existing module or exporting its private declarations to consumers of this module.
Updated the linear-extension node's proof and dependencies to record that reuse.
The item proof and all public signatures remain unchanged. The delivery tool rebases
the repaired sandbox on the fetched sheaf-dag before its preflight.

## Proved and sorry left
The original item hole in
`AlgebraicGeometry.exists_openOrdinaryTensor_pure_germ_coordinates` is closed by
identifying the specified ring equivalence and applying
`AlgebraicGeometry.openOrdinaryTensor_pure_germ_coordinates_linear_extension`.
The latter theorem is proved by scalar extension of the canonical unit-scalar equation.
The sole added and remaining hole is
`AlgebraicGeometry.openOrdinaryTensor_pure_germ_coordinates_canonical`
(node `lem-pc-open-ordinary-tensor-pure-germ-coordinates-canonical`).
Thus the original one-hole item is reduced to one strictly simpler unit-scalar
statement; this is a decomposition, not an unconditional proof of the generator
calculation. The remaining private `open_coordinate_smul` helper is fully proved.
This repair adds no holes and removes two duplicate proved helpers.

## No longer needed
The two duplicate private helper declarations are removed; their proofs are no longer
needed in the delivered module. No dependency module is pruned. The existing
OpenModuleStalkRestrictionComparison module is now reused for scalar compatibility.
The item directly needs the linear-extension node, which needs the canonical node
and the existing restriction comparison node. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong
The previous delivery re-proved two private helper statements already present word
for word in the library. Importing the existing comparison module with `import all`
allows the existing semilinearity theorem to be used directly. No visibility change
or forced consumer adaptation is necessary. The previous second reading passed the
duplicates; that reading is superseded and is not claimed for this repair.
The existing change record is
`coord/changes/exists_openOrdinaryTensor_pure_germ_coordinates.md`.

## New nodes
`lem-pc-open-ordinary-tensor-pure-germ-coordinates-canonical` records the remaining
unit-scalar generator equation (Stacks Tags 0098 and 0096).
`lem-pc-open-ordinary-tensor-pure-germ-coordinates-linear-extension` records the proved
scalar extension, now explicitly dependent on the canonical equation and
`lem-sc-open-module-stalk-restriction-comparison`. No further nodes were added.

## Second reading by S1
1. Compared both delivered modules with the repository versions. The target theorem
   signature is byte-for-byte unchanged; the canonical module is new, and its split
   theorem is recorded by its node.
2. Compiled the sandbox modules and checked that the only remaining `sorry` is the
   named canonical theorem. No forbidden declarations or hollow definitions were
   introduced; the proved target and linear-extension theorem use only the permitted
   imported results.
3. Checked the split statement against the target and small unit-scalar cases. It is
   the strict generator subcase needed by the linear extension and does not restate
   the target. Its source, proof description, and DAG node agree.
4. Read the proof from the top downward. The target reduces its ring equivalence by
   `RingEquiv.ext`; scalar extension uses the canonical generator equation and the
   existing stalk restriction comparison. The proof-only `import all` is used solely
   for the existing private helper, and duplicate private helpers were removed.
5. The DAG proof dependencies match the Lean proof, and the unit route remains through
   the canonical generator and linear-extension steps.

I changed only the proof/imports and linter options in the target module, added the
canonical split module and node files, and documented the second reading here.
