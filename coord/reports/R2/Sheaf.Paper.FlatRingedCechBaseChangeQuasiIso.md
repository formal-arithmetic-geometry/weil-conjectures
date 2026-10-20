## What changed

Repaired and proved `CategoryTheory.flat_ringedCech_baseChange_data_quasiIso` in
`Sheaf.Paper.FlatRingedCechBaseChangeQuasiIso`. The old universal assertion was already
marked STATEMENT-DISPUTED and is false. The replacement concerns the specified unit of
actual termwise scalar extension, as in Stacks Algebraization Tag 099I. The repair and
verbatim signatures are in `coord/changes/flat-ringed-cech-canonical-unit.md`.

Adapted the sole consumer, `Sheaf.Paper.FlatRingedCechBaseChange` (unclaimed), keeping its
entire theorem signature unchanged. It now takes actual scalar extension of K and the
adjoint augmentation. The adjunction equation proves augmentation compatibility.

Added four modules: the explicit termwise scalar-extension adjunction, the quotient-unit
criterion, ideal-power torsion for the ordered Koszul system, and the local comparison.
All are fully proved. The local proof identifies the underlying scalar unit with tensoring,
commutes scalar extension with slice restriction, applies the existing nilpotent-scalar
argument to ordered Koszul homology, passes through exact sequential colimits, and
transports through the given derived isomorphism. The global proof uses a finite generating
cover and `Sheaf.isIso_of_coversTop`. All six modules compiled cleanly together; the longest
file took 29.9 seconds in the last run, under the unchanged server limit.

## Proved and sorry left

Actual packet hole count: **0**. New holes: **0**. Split-off unfinished theorems: **0**.
The original item contained one hole, in
`CategoryTheory.flat_ringedCech_baseChange_data_quasiIso`. Its false original universal
statement is not proved and is not counted as an unchanged-statement proof. This delivery
repairs that statement and completely proves the corrected canonical-unit obligation.
The old holed statement is removed, rather than hidden in a new assumption or renamed
lemma. The unchanged parent theorem remains completely proved.

The following public results and construction are now complete:

- `CategoryTheory.flat_ringedCech_baseChange_data_quasiIso` (corrected statement).
- `CategoryTheory.exists_flat_ringedCech_baseChange` (unchanged statement, adapted proof).
- `CategoryTheory.RingedSiteIdeal.scalarExtension_unit_cokernel_isIso`.
- `CategoryTheory.ordered_koszul_ideal_power_annihilates_homology`.
- `CategoryTheory.flat_ringedCech_local_unit_quasiIso`.
- `CategoryTheory.ringedScalarExtensionComplexAdjunction` and its proved
  `CategoryTheory.scalarExtension_additive` instance.

No private helper has a hole. The new statements cover the empty generating list, arbitrary
integer cohomological degree, the zero ideal, and the zero ring. The ordered torsion bound
is positive even for the empty list. The local assertion assumes only a derived isomorphism;
the augmentation equation is needed only by the unchanged parent construction.

Existing library results, including exact slice restriction and the Koszul-colimit
isomorphism, are used as declared. Their proofs are not replaced or silently assumed in
new hypotheses. The delivery does not claim to eliminate all transitive library sorries.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `WeilConjectures.AlgebraicGeometry.SiteRestrictionExact`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat`.
- `Sheaf.Paper.FlatExtendedCechComparison`.

The first four direct proof imports were also removed from the adapted parent. Existing
public imports were retained. Slice flatness is genuinely needed by the local comparison
and is imported there. Some tensor infrastructure remains transitively needed by the
reused generic tensor proofs; removing a redundant direct import does not withdraw it.

The old node dependencies `lem-weil-pbc-flat-extended-cech-comparison` and
`lem-weil-pbc-site-restriction-exact` are not used on this route. The latter concerns a
different source-library site restriction interface; the proof uses exact module
`overFunctor` and Mathlib locality instead. The old scalar-extension-data dependency
`lem-weil-pbc-flat-ringed-cech-base-change-data` is unnecessary: the parent constructs the
complex and augmentation directly with the specified adjunction. No arbitrary scalar model
is chosen. The subset-indexed finite-stage comparison and its fraction identification
are unnecessary for the ordered complex: the proof applies the existing generic torsion
helpers directly to the ordered stages, then the existing ordered colimit isomorphism.

`Sheaf.Paper.FlatExtendedCechComparison` and its finite localization comparison chain are
not used by the new local proof. The generic proved helpers from
`Sheaf.Paper.FlatLocalizationKoszulCohomologyComparison` and
`Sheaf.Paper.FlatLocalizationKoszulHomotopy` remain used; those modules are not pruned.
No module is withdrawn and no global unreachability is asserted for the removed imports:
other consumers can still need them. The blueprint unit's statement and realized steps
are unchanged.

## Where the brief, the DAG or earlier work was wrong

The old universal statement inferred quasi-isomorphism solely from an augmentation
equation. For phi=id and I=0, take K=R[0] over a nonzero ring, L=K direct-sum K, u the first
inclusion and delta the first projection. The equation holds but H^0(u) is not surjective.
The empty-list local model is R[0]. Tag 099I specifies K prime=K tensor_R B instead. Its
canonical unit is the corrected result proved here. The earlier parent choice L=B[0]
with identity augmentation also fails in general; the new construction follows the source.
The only DAG citer and the only downstream Lean module are adapted together, preserving
the parent's exact statement and all Challenge statements.

The existing `FlatExtendedCechComparison` interface concerns a separate subset-indexed
Koszul/localization model. The local description here uses ordered tensor products.
Reusing the generic nilpotence and scalar helpers, while proving contraction on the ordered
model itself, avoids an unnecessary comparison between these two presentations.

Resume metadata observation: the original item claim is R2 at
2026-10-19T23:16:01Z (original session start 23:16:05Z). On resumption the sandbox `.budget`
reported a fresh start 1792498817.1094315 (2026-10-20T12:20:17Z), budget 7200, session 86400,
depth 2. The launcher supplied no additional attempt identifier. I did not edit that
metadata, retained the original 24-hour safety deadline, and continued proving. This
metadata lifecycle observation does not affect the mathematics or request a time waiver.

## New nodes

`def-weil-pbc-ringed-scalar-extension-complex-adjunction` records the explicit existing
scalar adjunction prolonged termwise, together with its proved additivity instance, in
`Sheaf.Paper.RingedScalarExtensionComplexAdjunction`. No existence witness is chosen.

`lem-weil-pbc-ringed-ideal-quotient-comparison` records the quotient-unit criterion in
`Sheaf.Paper.RingedIdealQuotientComparison`. Raw quotients and all comparison maps are
constructed, and their universal properties and local bijectivity are proved.

`lem-weil-pbc-ordered-koszul-homology-torsion` records the genuine ordered-stage contraction
and ideal-power annihilation argument in `Sheaf.Paper.OrderedKoszulHomologyTorsion`.

`lem-weil-pbc-flat-ringed-cech-local-unit-comparison` records the slice comparison in
`Sheaf.Paper.FlatRingedCechLocalComparison`, combining these ingredients with existing
flat-torsion and filtered-colimit results. It is fully proved, not another split-off hole.

Change record: `coord/changes/flat-ringed-cech-canonical-unit.md`. The item node carries the
statement correction and complete citer audit. Both existing proof nodes now describe
the actual canonical-unit route.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
