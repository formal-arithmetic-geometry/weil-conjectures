## What changed

Proved all six theorem declarations in `Sheaf.CategoryTheory.RingedSectionLocalization`:
`ringedSectionLocalization_isUnit`, `ringedSectionLocalizationMap_smul`,
`ringedSectionLocalizationLinearMap_id`, `ringedSectionLocalizationLinearMap_comp`,
`ringedSectionLocalizationPresheaf_one_natural`, and `ringedSliceSection_natural`.
The proofs use the localization unit, lift equations, and localization ring-hom
extensionality from Mathlib, together with the section naturality and slice triangle.
The existing public imports are retained because downstream declarations rely on the
module interface.

## Proved and sorry left

Six sorries closed: `ringedSectionLocalization_isUnit`,
`ringedSectionLocalizationMap_smul`, `ringedSectionLocalizationLinearMap_id`,
`ringedSectionLocalizationLinearMap_comp`, `ringedSectionLocalizationPresheaf_one_natural`,
and `ringedSliceSection_natural`. No sorries remain in the delivered module and none were added.

## No longer needed

No imports, DAG nodes, or additional modules were removed or added.

## Where the brief, the DAG or earlier work was wrong

None.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
