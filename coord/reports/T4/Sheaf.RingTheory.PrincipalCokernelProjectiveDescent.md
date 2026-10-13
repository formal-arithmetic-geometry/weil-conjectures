## What changed
Replaced the proof of `Module.injective_projective_cokernel_of_principal_cover`
with a complete Mathlib-based proof. The target signature and docstring are unchanged.
Added plain proof imports `Mathlib.RingTheory.Flat.Localization` and
`Mathlib.RingTheory.Flat.EquationalCriterion`. No new declarations or modules remain.

## Proved and sorry left
Closed the one original hole:
`Module.injective_projective_cokernel_of_principal_cover`.
Added zero holes. No `sorry` remains in the delivered module. The first worker's
`Module.injective_of_principal_cover` and
`Module.projective_cokernel_of_principal_cover` were both proved during review,
then inlined; their unlanded helper modules and nodes were removed.
The final target's axiom check shows only `propext`, `Classical.choice`, `Quot.sound`.

## No longer needed
All four old proof dependencies are replaced by direct Mathlib applications:
`lem-sc-affine-standard-cover-flat-localization-span`,
`lem-weil-pbc-finitely-presented-flat-module-projective`,
`lem-weil-pbc-flat-over-localization`, and `lem-weil-pbc-projective-module-flat`.
They are Mathlib-backed nodes, without Lean modules to prune. No existing import
was removed. The two proposed helper modules and split nodes were deleted before
landing; they therefore do not count as pruned library modules.

## Where the brief, the DAG or earlier work was wrong
The first worker's conjunction decomposition did not finish either mathematical
branch, increased the holes from one to two, and left the old target DAG proof
unchanged. Its new node proofs and docstrings were incomplete and its searches
were copied from the original node. Direct Mathlib localization and tensor
right-exactness lemmas suffice to close both branches; no split is needed.

## Second reading by T4
1. Compared the target declaration with the repository original by extracting its
   entire signature: byte-for-byte identical. Public imports, visibility, and all
   existing definitions are unchanged. No change record is needed.
2. Compiled the final module with `lcompile.py`, without warnings. Checked its axiom
   report: only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`. Scanned for
   forbidden declarations and holes: none. The local cokernel equivalence is
   Mathlib's constructed equivalence; no data is chosen from an unproved existence.
3. Searched with new wording through leanfinder, loogle, grep, and repository/upstream
   sources. Inspected the candidate signatures and used Mathlib directly. Both
   initial split obligations were closed and inlined, so no new statement remains.
   The proof covers empty prime spectra (the zero ring), zero modules, and arbitrary
   universe levels; it does not assume the modules themselves are projective.
4. The two new plain imports are used. Redundant explicit BaseChange and Exactness
   imports were removed. The four old proof dependencies are listed above. Inspected
   `dag/units/sk-prop-av-cube.json`: its `realized` statement and step arrays are empty;
   this target is a below-unit auxiliary, not a node realizing the unit statement.
   The cube theorem's route is unchanged.
5. Updated the target node's proof, proof dependencies, and origin to describe the
   actual unit-ideal-span injectivity argument, finite presentation of the quotient,
   tensor-cokernel equivalence, local flatness descent, and finite-presented-flat
   projectivity criterion. No new node or statement survives the repair.

Second reading changed the decomposition into a complete proof, inlined both
branches, deleted both split modules/nodes, corrected the DAG and progress report,
and minimized the proof imports.
