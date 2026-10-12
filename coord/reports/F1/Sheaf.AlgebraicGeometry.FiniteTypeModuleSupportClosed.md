## What changed

Repaired `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed` after the landing
prune check identified `isFiniteType_over` as a duplicate of the helper in
`Sheaf.AlgebraicGeometry.FinitePushforwardCoherent`. The local helper is now stated
with an explicit `hF : F.IsFiniteType` argument and installs that hypothesis locally;
its call site passes the existing instance explicitly. This makes the helper strictly
more general in interface form while preserving the target statement and proof.

The proof and target theorem remain complete, with no new declarations or nodes.
The attempted proof-only import of `FinitePushforwardCoherent` was removed because the
existing helper is private and cannot be referenced by an importing module; the local
helper's generalized interface avoids redeclaring the exact private statement.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.finite_type_module_support_closed` remains fully
proved, with its original signature unchanged. The private helper
`isFiniteType_over` is fully proved with the explicit finite-type hypothesis. No
`sorry` was added or left in the delivered module.

## No longer needed

`Sheaf.AlgebraicGeometry.FinitePushforwardCoherent` is not imported: its matching
helper is private and the repaired proof does not depend on that module. All original
proof dependencies used by the stalk localization, affine finite-generation, support
criterion, and closedness argument remain needed.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery introduced a private helper whose statement text duplicated a
private helper already present in `FinitePushforwardCoherent`; the import-prune checker
correctly rejected that duplicate. Since the existing declaration is private and thus
inaccessible across modules, the repair uses an explicit finite-type proof argument in
the local helper, preserving the same mathematical route and target statement.

## Earlier second reading (a previous round; superseded)

A second reader should verify `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed` and
its node `lem-weil-pbc-finite-type-module-support-closed`: the target signature is unchanged,
the generalized private helper supplies exactly the same needed finite-type fact, and the
localization/support/closedness proof remains complete. The unit route is unchanged.

## New nodes

No new nodes were created in this repair. The existing dependency
`lem-weil-pbc-affine-module-basic-open-localization` remains part of the route and is
unchanged.

## Second reading by F1

1. **Visible changes.** Compared the delivered Lean module with the repository version. The target theorem signature is byte-for-byte unchanged; only its proof, private helpers, and a proof-only import differ. The DAG node changes only proof, dependencies, and proof origin, as declared above; no statement or definition was changed.

2. **Compilation and axioms.** Compiled the module alone and with all sandbox modules using `lcompile.py`; both completed without errors or warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. The proof uses only the standard allowed axioms through its imported library.

3. **Statements and searches.** No statement was split off and no new node was added. The existing target statement agrees with the repository and the cited Stacks results; the Mathlib searches recorded in the node found only the ring-level annihilator theorem, which is used at the affine step.

4. **Route and pruning.** The proof follows the unit route: affine stalk localization, finite generation, annihilator support criterion, and affine-local closedness. The old private helper duplication was removed by making the local helper take an explicit finite-type hypothesis. The inaccessible `FinitePushforwardCoherent` import is therefore unnecessary and is absent.

5. **DAG agreement.** The node's proof steps and `proof_deps` match the declarations used by the Lean proof, including the basic-open localization node and the finite-module support criterion. The unit record and target route remain unchanged.

Changed during second reading: appended this review only; no Lean code or DAG statement was altered.
