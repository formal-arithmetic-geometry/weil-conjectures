## What changed

Proved both existing theorems without changing either signature, and proved the new tensor comparison. The retained étale proof uses geometric fibers. The new pro-étale proof transfers through the published intrinsic constant-ring realization, detects the kernel of each tensored monomorphism by the complementary fixed-scalar pullbacks, and uses the open unit, closed counit and disjoint-range vanishing for the two preservation assertions. The canonical pullback comparison is `openSquarePullbackModel`; direct image uses `sfIntrinsicDirectImageComparison` and the canonical coefficient-map equation.

The theorem docstrings describe the geometric-fiber and fixed-scalar kernel arguments actually formalized. Private proved helpers establish invariance of site flatness under isomorphism, transport flatness through the tensor comparison, and prove fixed-scalar flatness detection. The compiler checks both delivery files in dependency order. Validation: both files, an independent importer applying both theorems at their original signatures, and the three unchanged direct consumers (`SupportQuotientFlat`, `SupportedProductLocalization`, `FlatModelGeneration`) compile cleanly through `lcompile.py`. `#print axioms` for the étale theorem contains only `propext`, `Classical.choice`, and `Quot.sound`; the pro-étale theorem and tensor comparison additionally inherit `sorryAx` from existing imported obligations. No new axiom or hole is introduced.

No definition or existing statement changed. The public import removal is recorded in `coord/changes/B3-open-closed-flatness-proof-imports.md`, including the 451 transitive consumers checked on resumption.

## Proved and sorry left

Closed both original holes: `AlgebraicGeometry.openClosedFlatness_etale` and
`AlgebraicGeometry.openClosedFlatness_proEtale`. The new theorem
`AlgebraicGeometry.proEtale_intrinsic_tensorRight_comparison` is also proved, from
`PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses`, the proved
`siteSheafTensorRightIso`, and the explicit fixed-scalar sheafification bridge.
There are zero remaining `sorry` declarations in either delivered Lean file and zero
new holes. This closes two of two original holes; no obligations are split off.
Existing imported statements may still depend on `sorry`, as intended by stage 3.

## No longer needed

Removed `public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`, and the unused proof imports `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback`, `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`, `Sheaf.CategoryTheory.ModulePullbackTensorIso`, `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`, `WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion`, `WeilConjectures.SixFunctors.OpenClosed.Complex`, and `WeilConjectures.SixFunctors.OpenClosed.Vanishing`. The proof uses fixed-scalar kernel detection instead of the ringed localization sequence and all three exactness defects. The following original proof dependencies are unnecessary for this proof: `prop-weil-pbc-inverse-image-modules-exact`, `lem-weil-pbc-proetale-immersion-limit-preservation`, `lem-weil-pbc-ringed-topos-flat-module-pullback`, `lem-weil-pbc-ringed-topoi-module-pullback-tensor`, `lem-weil-pbc-proetale-ringed-open-closed`, and `lem-weil-pbc-open-closed-short-exact`. Removed obsolete top-level `tool_uses` entries for these dependencies, preserving the order of remaining approvals. Their corresponding statement modules are not added as proof imports; existing public imports needed by the signatures are retained. Dependencies needed elsewhere are unaffected.

Discarded the earlier attempt's three unsubmitted split modules and nodes (`ProEtaleFlatnessRestriction`, `ProEtaleFlatnessExtensionByZero`, `ProEtaleFlatnessPushforward`). None has landed in the shared repository, so no repository file is withdrawn. Their three clause-level holes are eliminated; the shared tensor interface is proved here. The retained draft also cited `lem-exc-constant-inverse-image-flat`, which concerns the étale-to-pro-étale comparison rather than scheme pullback, and `lem-exc-open-closed-detection`, whose current Lean interface concerns arbitrary ring sheaves. Those two proof dependencies are removed and replaced by exact attachments to the source declarations actually used; their modules are not imported.

## Where the brief, the DAG or earlier work was wrong

The retained DAG draft cited the comparison-pullback lemma for scheme pullback, and cited an arbitrary ring-sheaf detection interface for the fixed-scalar source theorem. Three source-library attachments now record the exact tools used, without new Lean declarations or holes. The earlier attempt split the three pro-étale clauses directly and supplied no proof of their shared mechanism. This delivery writes that mechanism in Lean. The generic ringed-topos tensor declaration in the original plan uses coincident site universes and does not directly instantiate to the small pro-étale site. The fixed-scalar realization avoids that mismatch while keeping ordinary sheaves and the original canonical operations.

The proof uses the existing closed-counit tool `lem-exc-proetale-closed-fully-faithful`, the canonical pullback comparison of `lem-trf-open-square-exchange`, and the local equational criterion. The geometric-fiber criterion and fixed-scalar pro-étale pullback and zero-detection tools are recorded by new attachments to their existing source declarations. These are used as tools, without bypassing a realized statement or step of this unit. The unit's `realized` lists are empty. No maintainer approvals were added; only obsolete top-level entries were removed. The new proved tensor lemma also uses `lem-weil-pbc-independent-sheaf-tensor-colimits` for the explicit-site/monoidal tensor comparison.

## New nodes

`lem-sfb-proetale-intrinsic-tensor-comparison` records the tensor comparison for the existing intrinsic realization, in `Sheaf.SixFunctors.ProEtaleIntrinsicTensorComparison`. It is independent of complementary immersions and is proved in this delivery. The statement includes the zero ring, empty scheme and zero sheaf; the balanced-tensor and sheafification universal properties cover these cases. Its LeanSearch, Loogle, LeanFinder and grep searches were run through `msearch.py`. Change record: `coord/changes/B3-open-closed-flatness-proof-imports.md`, for removal of an unused public import and the lexical monoidal namespace opening; no declaration signature changes.

`lem-sfb-etale-flat-geometric-fibers` attaches the existing
`AlgebraicGeometry.Etale.flat_iff_forall_flat_sheafFiber_obj`; its source module also
contains the three-line consequence that étale inverse image preserves flatness.

`lem-sfb-proetale-fixed-scalar-pullback-flat` attaches the existing
`AlgebraicGeometry.ProEtale.upperStarPreservesFlat_moduleCat`, with its Noetherian
hypothesis stated explicitly (finite coefficients satisfy it).

`lem-sfb-proetale-fixed-scalar-zero-detection` attaches the existing
`AlgebraicGeometry.ProEtale.isZero_of_isZero_upperStar_of_isCompl` for fixed-scalar
module sheaves. It records the typed source interface used here; the existing
`lem-exc-open-closed-detection` keeps its broader arbitrary ring-sheaf statement and
attachment unchanged. These three nodes add no Lean files, declarations or holes.
Their natural-language, LeanFinder and Mathlib grep searches ran through `msearch.py`;
the blueprint searches for “flatness stalk” and “open closed detection” found no
matching statement; “flat sheaf” found only the flatness definition `pur9-def-flat-sheaf`.
All three attached source declarations were checked by `#print axioms` and use only
`propext`, `Classical.choice` and `Quot.sound`. The zero ring, empty scheme and empty open or closed
member require no exceptions: geometric-point quantification may be vacuous, and
the finite jointly surjective detection proof handles the two degenerate pairs.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
