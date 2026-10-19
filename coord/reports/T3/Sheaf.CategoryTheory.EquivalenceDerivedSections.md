## What changed

Replaced the proof hole in `CategoryTheory.exists_equivalence_derivedSections` in
`Sheaf.CategoryTheory.EquivalenceDerivedSections` with the stated injective-resolution
argument. The signatures, universes, public imports, and real-data construction
`InjectiveResolution.equivalenceImage` are unchanged.

For each resolution, conjugate the homology isomorphism induced by `α` by Mathlib's
`isoRightDerivedObj` isomorphisms. Lift object morphisms with `InjectiveResolution.desc`;
its termwise image under `E` respects the transported augmentations. Applying Mathlib's
hom and inverse naturality formulas proves naturality even for two independently chosen
resolutions. The identity case proves independence and the required formula for every
resolution. In degree zero, cancel the cycles inclusion and use naturality on the
augmentation; `toRightDerivedZero_eq` then gives the exact canonical normalization.

The existing seven-step DAG plan is followed, so no node changes are needed.

## Proved and sorry left

Closed: `CategoryTheory.exists_equivalence_derivedSections`
(node `lem-exc-equivalence-derived-sections`), the module's one original hole.
Added: none. Left: none. No intermediate statements were split off.
The final single-file `lcompile.py` check passed in 2.2 seconds with no errors or warnings.
The delivery dry run also checks all declaration axioms and the unchanged interfaces.

## No longer needed

None. All existing imports and all declared proof dependencies remain relevant to the
original resolution argument. No modules or nodes are pruned.

The source library's `Functor.rightDerivedCompIsoOfExact` supplies an abstract comparison,
but its derived-category construction would still require the resolution formula and
normalization proved here. The direct Mathlib resolution argument avoids those additional
imports.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The unit route and the full original statement are
preserved, including the arbitrary-resolution formula and equality with the given `α` in
degree zero.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
