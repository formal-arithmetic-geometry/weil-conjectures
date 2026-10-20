## What changed

Repaired every point of return C-15179 (returned head `15179a969e`).
Removed the proposed restoration of
`lean/Sheaf/AlgebraicGeometry/ScalarAbelianPullbackSquare.lean` from this packet:
its official WeilConjectures twin already provides the same declarations and
complete proof. The quarantined archive is untouched, and its already-absent
active path is not added to `deleted.txt`.

Repointed `new-sc-scalar-abelian-pullback-square` to the official module and file,
set `lean.existing` to true, and used the reviewer's requested `lean.note`
verbatim. Its statement, proof, dependencies and unit route are unchanged.
Updated the change record's Users row accordingly.

Preserved the approved retirement of
`Sheaf.AlgebraicGeometry.ScalarAbelianExtFactorization`: `deleted.txt` withdraws
only that duplicate, and its node points to its proved official twin. Comparison
with current shared source confirms that the twin preserves A2's
`ExtExactFunctorIdentityComparison` import and `exactFunctorIdentityComparison`
proof. No source-library file or target statement changes.

Validation: lcompile.py --all accepted unchanged current copies of the official
factorization, pullback square, forget-pullback adjunction, forget-pullback
comparison and structure-coefficient adjunct (exit code 0; no warnings).

Change record:
`coord/changes/retire-scalar-abelian-ext-factorization-V2-20261020.md`.

## Proved and sorry left

Holes closed: 0 of 0. Holes added: 0. Holes left: none in the withdrawn item.
No theorem is split off.
`AlgebraicGeometry.Scheme.scalar_unit_abelian_ext_factorization` and
`AlgebraicGeometry.Scheme.scalar_abelian_pullback_square` retain their complete
proofs in the official modules. No definition is hollowed.

## No longer needed

Withdrawn module: `Sheaf.AlgebraicGeometry.ScalarAbelianExtFactorization`.
No active library module imports it. The returned packet's proposed
`Sheaf.AlgebraicGeometry.ScalarAbelianPullbackSquare` restoration is removed;
its node now references the official counterpart as the reviewer requested.
The historical quarantine archive remains preserved.

The factorization duplicate's five imports leave that duplicate file only:
`WeilConjectures.AlgebraicGeometry.ScalarUnitCohomologyComparisonFamily`,
`WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisExtFunctorSquare`,
`WeilConjectures.CategoryTheory.ExtExactFunctorIdentityComparison`,
`Mathlib.CategoryTheory.Sites.Adjunction`, and
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`.
All remain in the official proof; no mathematical dependency node is pruned.
All parent dependency edges and the unit route remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The returned packet restored a quarantined Sheaf pullback-square module even
though its official twin already contains the same full declaration names.
That would preserve a duplicate and conflicts with the human's retirement
instruction and retire item 1492. Return C-15179 explicitly requires the official
node attachment instead. This repair follows that instruction without deleting
or modifying the quarantine archive.

The earlier return also required preserving A2's later identity-comparison
adaptation. The current official factorization retains that adaptation; the
approved item retirement and its node attachment remain in this packet.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
