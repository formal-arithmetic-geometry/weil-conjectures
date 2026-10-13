## What changed

Proved `RingTensorCohomology.baseLocalizationCohomologyMap_isIso` with its signature,
visibility and public imports unchanged. The proof establishes the universal property of
the restricted derived functor using its counit on K-flat complexes, applies uniqueness of
left derived functors to the canonical lift, and maps the resulting isomorphism through
B-homology and the two model identifications.

Added `Sheaf.Algebra.Homology.LocalizationRestrictionKFlat` with the fully proved theorem
`ModuleCat.kFlat_restrictScalars_of_isLocalization`. Exact localization sends each
R-quasi-isomorphism to an Rp-quasi-isomorphism. Tensoring with the K-flat Rp-complex,
restricting scalars, and conjugating by the existing mixed-tensor restriction comparison
proves preservation by tensorRight; braiding proves preservation by tensorLeft.

Only proof imports were added to the item's module: the new restriction lemma,
`import all Sheaf.Algebra.Homology.KFlatScalarExtensionDerivedIso` (to reuse its existing
proved scalar-extension helper), the source-library universal derived characterization,
functorial flat resolutions, and ModuleCat exact-colimit instances. No existing definition,
statement, target, instance, or visibility was changed. Updated the item's DAG proof route.

Both delivered modules compile individually in under 10 seconds. The existing derived
isomorphism helper is used rather than reimplemented. The Stacks pages 06Y6, 00CS and
0DJ8 were read online because this clone has no literature source files:
https://stacks.math.columbia.edu/tag/06Y6,
https://stacks.math.columbia.edu/tag/00CS,
https://stacks.math.columbia.edu/tag/0DJ8.

## Proved and sorry left

Closed the sole original hole:
`RingTensorCohomology.baseLocalizationCohomologyMap_isIso`
(node `lem-pc-base-localization-cohomology-is-iso`).

Added and completely proved:
`ModuleCat.kFlat_restrictScalars_of_isLocalization`
(node `lem-pc-localization-restriction-kflat`).

No sorry remains in either delivered module; no holes were added or split off.
This closes one hole rather than decomposing it. The dry run's axiom probe checks the
transitive axioms, including those of the reused source-library declarations.

## No longer needed

Removed the planned direct dependencies `lem-pc-kflat-scalar-extension-counit`
(module `Sheaf.Algebra.Homology.KFlatScalarExtensionCounit`) and
`lem-weil-pbc-localization-module-exact` (Mathlib `LocalizedModule.map_exact`).
The former is replaced by direct use of the existing universal K-flat characterization;
the latter by Mathlib `IsLocalization.flat` and exact flat scalar extension inside the
proved restriction lemma. They need not be imported or separately proved for this item.
This is pruning of this proof branch, not a claim that other targets no longer use them.

No original import was removed: the sole public import `BaseLocalizationMap` is needed
by the statement and its canonical map. Removed a redundant trial proof import of
`Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed`, already public in the new helper.
No other planned nodes are bypassed. `BaseLocalizationMap`, the mixed-tensor restriction
comparison, and the scalar-extension K-flat helper remain used.

## Where the brief, the DAG or earlier work was wrong

The DAG's proof was mathematically sound but did not expose the K-flat restriction step
as a Lean theorem. The new lemma makes that step explicit and is itself fully proved.
Choosing a resolution of each input and transporting invertibility is unnecessary:
the existing universal characterization proves the restricted functor universal on all
K-flat complexes, and uniqueness makes the canonical lift an isomorphism globally.
This preserves the localization/K-flat computation route and the unit's statement and steps.

Edge cases impose no extra hypotheses: zero complexes, identity localization, and
localization at a submonoid containing zero are covered by the same exactness,
arrow-isomorphism, and universal-property proofs. Arbitrarily unbounded complexes are
allowed. No flatness of A, B, or D is introduced. Existing signatures remain identical.

Searches: LeanFinder for derived tensor over a localized base returned only ordinary
localization tensor equivalences; Loogle returned no generic derived-lift match.
For the new lemma, LeanSearch returned Internal Server Error; LeanFinder returned
module-flatness facts and exact flat extension, but no K-flat restriction theorem.
Mathlib/library grep and blueprint searches found no duplicate restriction lemma.
The existing `MixedTensorRestrictionComparison` supplies the necessary total tensor API.

## New nodes

`lem-pc-localization-restriction-kflat`, in the item's chapter and unit, records the new
fully proved restriction theorem in `Sheaf.Algebra.Homology.LocalizationRestrictionKFlat`.
Its only mathematical inputs are exact localization, the K-flat predicate, and the already
proved mixed-tensor restriction comparison. Its statement has no cohomology models,
derived-functor universality, B, A, D, or cohomological degree; it is precisely the smaller
K-flat restriction step of the original plan. No change records or forced adaptations
are needed because all existing interfaces are unchanged.

## Second reading by R4

1. Compared both delivered modules with the repository versions. Existing declaration
signatures and visibility are unchanged; only proofs and proof imports changed, plus the
new restriction module and node described above.
2. Compiled both modules with `lcompile.py --all`; compilation succeeds with no errors.
There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions in the
delivered files. The proofs use only the permitted transitive axioms.
3. Checked the split statement against the K-flat definition and localization edge cases
(identity, zero and unbounded complexes); it is strictly smaller than the target and has a
complete source-backed proof and matching DAG node. Searches found no duplicate declaration.
4. Reviewed the proof route top-down: it uses the existing mixed-tensor comparison and
K-flat scalar-extension result, and removes only the two dependencies listed above. The
unit route and all target-facing statements are retained.
5. The DAG proof steps and `proof_deps` match the Lean proofs, including the new node and
its module record. No statement or definition change record is required.

Changed only proof imports and proof text; no mathematical or interface changes were needed.
