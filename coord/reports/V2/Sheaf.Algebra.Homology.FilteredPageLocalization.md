## What changed

Restored `lean/Sheaf/Algebra/Homology/FilteredPageLocalization.lean` from its rework
quarantine archive. Repaired the assigned upstream API break in
`CategoryTheory.finiteFilteredCohomology`: both functor-law proofs now use
`FilteredObject.Hom.mk`, the constructor of the current canonical category,
instead of the removed `HomPreservingSteps.mk`. The two underlying homology equations
and all object/map data are unchanged. All 28 declarations and every import survive.

Proved the existing quotient-projection theorem with `cokernel.π_desc` and the
successive cohomology-image inclusion with `imageSubobject_comp_le`, cohomology
functoriality, and `Subobject.ofLE_arrow`. The elementary proofs apply unchanged
to zero objects, the zero ring, and arbitrary filtration and cochain indices.
Updated only the item's `lean.note`; the DAG route and dependencies are retained.
Change record: `coord/changes/V2-filtered-page-localization-canonical-hom.md`.

The restored module compiled alone through `lcompile.py` in 8.4 seconds, exit 0,
with no diagnostics. No library build was run. The quarantined
`Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence` is the sole source importer
found across live and quarantined sources; it requires no signature adaptation.
Its DAG parent still uses this node. This is a rework repair, not a withdrawal.

## Proved and sorry left

Original archive: 3 theorem holes. Closed 2; added 0; split off 0.

- Proved `CategoryTheory.finiteFilteredPageTransition_projection`
  (node `lem-kun-filtered-page-localization`).
- Proved `CategoryTheory.finiteFilteredCohomologyImage_succ_le`
  (node `lem-kun-filtered-page-localization`).
- Remaining existing hole: `CategoryTheory.filteredPageLocalization`
  (node `lem-kun-filtered-page-localization`), still exactly `:= by sorry`, with its
  original source and complete eleven-step proof docstring. This delivery completes
  the assigned compile repair and does not claim the full localization theorem proved.

The repaired `finiteFilteredCohomology` definition has no sorry fields. Neither of
the two completed theorem proofs uses an additional unproved lemma. The delivery
probe checks the axioms of all restored declarations.

## No longer needed

None. No imports, modules, DAG dependencies or approved tool uses are pruned.
The quarantined parent and all 28 public item declarations are preserved.
The proofs of the two elementary auxiliary lemmas need only the existing Mathlib
cokernel, image and cohomology APIs; the remaining dependency plan still belongs
to the existing unfinished localization theorem.

## Where the brief, the DAG or earlier work was wrong

The archived functor laws referred to the removed compatibility structure
`FilteredObject.HomPreservingSteps`. After the source sync the category uses
`FilteredObject.Hom`, so the old constructor names failed to elaborate. Replacing
those names repairs the assigned defect without changing any mathematical data.
There is no false statement or unit-route change. The live absence of this module
was quarantine, not permission to delete its declarations or abandon its parent.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
