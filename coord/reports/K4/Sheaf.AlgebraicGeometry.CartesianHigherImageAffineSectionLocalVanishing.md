## What changed

Completed the listed retirement of
`Sheaf.AlgebraicGeometry.CartesianHigherImageAffineSectionLocalVanishing`.
`deleted.txt` withdraws the duplicate module. The existing node
`lem-sc-cartesian-higher-image-affine-section-local-vanishing` is attached to
`WeilConjectures.AlgebraicGeometry.CartesianHigherImageAffineSectionLocalVanishing`,
with its declaration and statement unchanged and `existing: true`.

Compared all declarations and proofs. Only the copyright header and the unused
`_hc` binder in `cartesianHigherImage_section_eq_zero_of_finite_cover` differ.
The canonical upstream version needs no limit proof for sheaf separatedness;
the old signature follows by omitting that argument. Both local-vanishing theorem
signatures and all proof bodies agree verbatim. No upstream source was edited.

Change record: `coord/changes/K4-cartesian-higher-image-local-vanishing-retirement.md`.

## Proved and sorry left

This is a duplicate-retirement repair with zero original holes. Holes closed: 0.
Holes added or split off: 0. Holes left in the withdrawn module: 0.
No new mathematical proof is claimed.

The upstream replacements remain proved in their existing module:

- `AlgebraicGeometry.Etale.cartesianHigherImage_section_eq_zero_of_finite_cover`.
- `AlgebraicGeometry.Etale.cartesianHigherImage_affine_section_local_zero_sieve`.
- `AlgebraicGeometry.Etale.exists_cartesianHigherImage_affine_section_local_zero`.

The scratch validation applies these replacements to all three old signatures
and imports/checks the existing upstream parent. `lcompile.py` succeeded in 8.4 s
(exit code 0). Its only warning is the scratch file containing exclusively private
declarations; the scratch file is not part of the delivery.

## No longer needed

Pruned module:
`Sheaf.AlgebraicGeometry.CartesianHigherImageAffineSectionLocalVanishing`.
Its duplicate private comparison construction and proof helpers are retired too.

Its imports disappear with the duplicate file:

- `WeilConjectures.AlgebraicGeometry.CartesianHigherImageTransitions`.
- `WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit`.
- `WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf` (`import all`).
- `WeilConjectures.AlgebraicGeometry.CartesianHigherImageFiniteRawClassVanishing`.

These modules remain dependencies of the preserved upstream implementation.
No mathematical nodes or dependencies become unnecessary. In particular, this
retirement does not prune the finite raw-class obligation or any lower theory.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed module, whereas this current item is
listed in `coord/retire-items.tsv` and has zero textual holes. Its DIFFERENT flag
records the extra unused `_hc` argument, not a missing proof. The retirement
listing's old Sheaf parent has already been replaced by the upstream parent.

The stale node attachment is repaired. The sole actual DAG parent,
`lem-sc-cartesian-higher-image-affine-section-vanishing`, already attaches to
`WeilConjectures.AlgebraicGeometry.CartesianHigherImageAffineSectionVanishing`,
which imports the canonical replacement and uses its correct signatures.
The DAG parent edge and unit route are preserved. No current or quarantined Lean
module imports the retired twin; `tools/downstream.py` also reports zero users.
No forced adaptations or new nodes are required.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
