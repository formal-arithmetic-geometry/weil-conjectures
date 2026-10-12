## What changed
Added `Sheaf.AlgebraicGeometry.KoszulRestrictionZeroBase`, isolating the unshifted
restriction vanishing statement, and proved the shifted target from it using the
shift functor and the canonical commutation isomorphism. The target now imports the
base module privately.

## Proved and sorry left
The target theorem `AlgebraicGeometry.isZero_restrict_shift_koszul` is proved.
The new theorem `AlgebraicGeometry.isZero_restrict_koszul_base` remains a single
sorry, corresponding to node `lem-pc-koszul-restriction-zero-base`.

## No longer needed
None; the existing target imports remain needed for the statement and the base
statement.

## Where the brief, the DAG or earlier work was wrong
The original DAG proof combines contraction, sheaf gluing, and derived-category
vanishing in one target. The shift step is formal and was split off from that
mathematical core.

## New nodes
`lem-pc-koszul-restriction-zero-base` records the unshifted contraction and gluing
statement in `lean/Sheaf/AlgebraicGeometry/KoszulRestrictionZeroBase.lean`.

## Earlier second reading (a previous round; superseded)
The shifted theorem has the unchanged target signature and follows formally from the
unshifted statement via `Functor.map_isZero` and `commShiftIso`. The new base
statement is exactly the unshifted component required by this proof; its sorry is
tracked by the new node.

## Second reading by E3

1. Compared both delivered modules with the repository versions. The target theorem signature is byte-for-byte unchanged; the added base module is new, and no existing declaration was altered. Verdict: pass.
2. Compiled both modules with `lcompile.py --all`; compilation is clean. The target has no `sorry`; the sole remaining `sorry` is the named base theorem, with no forbidden declarations or hollow definitions. Verdict: pass.
3. Checked the base statement against the unshifted case of the target and the cited Stacks contraction/gluing argument. It is true and strictly simpler than the target, and its node and docstring identify the source. No duplicate library theorem was found. Verdict: pass.
4. The target proof uses the base theorem, `Functor.map_isZero`, and `commShiftIso`; this is the shortest formal shift reduction. All original public imports remain needed for the statement, while the base import is private and proof-only. Verdict: pass.
5. Updated the target node proof and proof dependencies to record the actual base-plus-shift route. The unit route is preserved: the new base node realizes the unshifted component and the target supplies the shift step. Verdict: pass.

Changed the target DAG proof metadata and added this second-reading record. No Lean proof changes were needed.
