## What changed

Added the proof-only import `Sheaf.AlgebraicGeometry.AffineBasePieceTensorBaseChangeInstance`.
The target theorem applies the new fixed-test-object intermediate theorem. The new theorem
contains the remaining geometric argument as a named `sorry`.

## Proved and sorry left

`AlgebraicGeometry.affine_base_piece_tensor_base_change` is reduced to the strictly smaller
`AlgebraicGeometry.affine_base_piece_tensor_base_change_instance`.
The latter remains `sorry`; node `lem-weil-pbc-affine-base-piece-tensor-base-change-instance`.

## No longer needed

None; the target's existing public imports remain required by its statement.

## Where the brief, the DAG or earlier work was wrong

The DAG plan omits a readily expressible fixed-test-object intermediate statement; the
full geometric pasting and tensor comparison could not be closed directly from the exposed
interfaces in this session.

## Earlier second reading (a previous round; superseded)

Pending second reading; the theorem is a strict fixed-test-object reduction and compiles.

## New nodes

`lem-weil-pbc-affine-base-piece-tensor-base-change-instance` records the fixed-test-object
intermediate theorem in `AffineBasePieceTensorBaseChangeInstance.lean`.

## Second reading by B3

1. Compared the delivered target module with the repository version. The target declaration
   signature is unchanged byte for byte; only a proof-only import and its proof body changed.
   Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; they compile without errors or
   warnings. The only remaining `sorry` is the named intermediate theorem
   `affine_base_piece_tensor_base_change_instance`, and no definition contains `sorry`.
   Verdict: pass.
3. Checked the split statement and its node. The intermediate theorem is a fixed test-object
   instance (the test object and compatibility equation occur inside the final conclusion),
   so it is a proper reduction rather than a second theorem with the target's outer test-object
   quantifier. Its source, blueprint, and docstring are recorded, and no duplicate declaration
   was found in the library. Verdict: pass.
4. The target proof follows the shortest available route in this delivery: it applies the
   fixed-instance reduction; the geometric construction remains explicitly named at that
   lower node. Existing public imports are still needed by the target statement, and the
   proof-only import is private. Verdict: pass.
5. The fixed-instance node remains on the unit's affine calculation route, and the node's Lean
   declaration matches the delivered module. Verdict: pass.

I changed the fixed-instance theorem's conclusion to expose one fixed test object inside the
reduction, updated the target application accordingly, and added this second-reading record.
