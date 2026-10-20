## What changed

Repaired the returned route by restoring `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
and the four consumer modules to their published versions. The target now publicly imports
`Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses` and specializes its
independent-universe `CategoryTheory.RingedHomUniverses.ringedInternalHom_exact`
interface at site universes `(u + 1, u)`, coefficient universe `u + 1`, and derived
universe `w`.

the new module `Sheaf.Algebra.Homology.RingedInternalHomExactUniverses`,
which carries the independent-universe two-clause `ringedInternalHom_exact` interface
while importing the unchanged S6 shift module. The target theorem keeps its original signature and
conjunct order. The new split interface and its users are recorded in
`coord/changes/A4-ringed-internal-hom-exact-universes.md`. The proper-base-change node records these declarations and the
specialized proof route.

Validation: the modified shift module and target module compile with `lcompile.py`.
The restored consumers no longer contain the forced universe annotations or telescope
rewrite from the returned delivery.

## Proved and sorry left

Closed the target hole `AlgebraicGeometry.Etale.sf_internalHom_triangulated`.
Zero sorries remain in the target module.

The existing shift-module sorries remain, including `rightShift_existsUnique`,
`leftShift_existsUnique`, and `hom_isTriangulated`. The new intermediate theorem
`CategoryTheory.RingedHomUniverses.ringedInternalHom_exact` remains a named sorry
with node `lem-weil-pbc-ringed-internal-hom-exact-universes`; it is strictly more
general than the target specialization and supplies both variance clauses. No sorry occurs in a definition, and no new target hole is introduced.

## No longer needed

The public import and generalized interface changes in
`Sheaf.Algebra.Homology.RingedInternalHomExactRestriction` are no longer needed.
The four consumer adaptations and the telescope elaboration change are no longer
needed. The private telescope compatibility API and all associated change-record
claims from the returned delivery were removed.

## Where the brief, the DAG or earlier work was wrong

The returned route generalized `ringedInternalHom_exact` in
`RingedInternalHomExactRestriction`, which changed downstream typeclass elaboration
and broke three published consumers. The independent-universe exactness belongs in
the already recorded `RingedInternalHomShiftOfUniverses` module, while the original
restriction module and theorem signature must remain unchanged.

## New nodes

`lem-weil-pbc-ringed-internal-hom-exact-universes` records the independent-universe
exactness intermediate theorem used by the target. Its proof is the existing cone
argument with independent universe parameters and remains split for a subsequent
worker.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
