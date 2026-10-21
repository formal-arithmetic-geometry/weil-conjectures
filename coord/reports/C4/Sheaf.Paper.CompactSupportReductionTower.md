## What changed

Constructed the tower functor as coefficient reduction followed by native open extension, separately right-derived proper image, and exact completed coefficient restriction. The existing theorem `WeilConjectures.exists_compactSupportReductionTower` keeps its statement unchanged. Its proof constructs the normalized scalar structures, proves scalar linearity of all four factors, supplies the triangulated structure and natural evaluation isomorphisms, and pastes the all-pair transition squares.

The horizontal coefficient transition is a real section-map construction. `compactSupportQuotient_eq` identifies its ring map with the direct quotient; `compactSupportCoefficientTransition_restricted` proves compatibility with the actual completed-module tower transition by exact localization. The input reduction transition is proved from the calculus unit-projection law and the coefficient adjunctions. These arguments do not assume that evaluation or quotient restriction preserves K-injectives.

The final pasting uses two proved abstract category lemmas in the item file. Derived functors are locally irreducible in the existence proof, so it uses their comparison API without unfolding the chosen resolution constructions.

The sandbox batch compile passed all five modules: the item took 37.8 seconds and the coefficient-transition module 31.9 seconds. The original named instance binders `linearX` and `linearY` are preserved; the unused-variable linter is disabled locally for this theorem to avoid renaming its binders. A subsequent single-file check of the item passed without warnings in 33.8 seconds. The delivery command performs the final compile, axiom and packet checks.

The original coefficient declarations were moved verbatim to `CompactSupportReductionTowerData`, publicly imported by the original module. The original coefficient-finiteness unit import also stays explicit in the item header. `CompactSupportNativeSystemEvaluation` constructs its two ordinary model comparisons and its derived evaluation isomorphism. `CompactSupportNativeSystemTransition` isolates the geometric coefficient square for arbitrary systems. Change record: `coord/changes/C4-compact-support-reduction-tower-native-construction.md`. No source-library declaration or target changes.

## Proved and sorry left

Closed the original hole of `WeilConjectures.exists_compactSupportReductionTower` by a complete combining proof. Added one hole: `WeilConjectures.compactSupportNativeSystemTransition` in node `lem-weil-compact-support-native-system-transition`. This is a decomposition: one upper hole closed and one strictly separate geometric hole added, net zero direct holes. It is not reported as a net proof advance. The item module and the other three new modules contain no `sorry`.

The remaining statement is the geometric transition identity for an arbitrary coefficient system. It asserts no completed-input reduction functor, no existence of a tower, no exactness or integral linearity, and no scalar structures. It is needed only at the final pasting step. Its docstring and node give the open-adjunction argument, proper K-injective normalization argument and their composition. The other substantial parts of the original assertion are now proved. Existing imported theorems with holes, including the coefficient evaluation calculus, remain their existing items; none is duplicated here.

Proved public results: `compactSupportProjection_comp` (preserved), `compactSupportQuotient_eq`, `compactSupportModuleRes_eq`, `compactSupportHorizontalRingSquare`, `compactSupportCoefficientTransition_restricted`, and the original existence theorem from the listed geometric lemma. The new model comparisons, quotient/horizontal maps, derived transition and evaluation are constructed without holes. Private scalar, projection-composition, adjunction-transition and reduction-transition helpers are completely proved.

## No longer needed

No module is withdrawn; global pruning of a module is not claimed. `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` remains a direct public import to preserve its unit-route occurrence. Original public coefficient imports remain available through the data module. Removed redundant draft imports of CoefDerivedSystemEvaluationCalculus, VaryingRingOperations and CompactSupportNativeSystemEvaluation from the main module, since the native transition dependency exposes their required API. Removed the draft unused import of ProEtaleConstantOpenSquareExchange from the coefficient-transition module (VaryingRingOperations is retained for its universe-normalized system instances), and the unused proof import of SystemPushforwardRestrictionTransition plus duplicate public imports from the geometric statement module.

Original private proof imports removed from the item (some remain transitive dependencies of existing APIs):

- `Sheaf.CategoryTheory.DiagramSiteRealization`.
- `Mathlib.Algebra.Category.Grp.FilteredColimits`.
- `Mathlib.CategoryTheory.Sites.Limits`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.Paper.RingedTopoiDerivedPullback`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`.
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars`.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
- `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.Paper.CoefficientSystemDerivedComparison`.
- `Sheaf.Paper.SemilinearDerivedSections`.
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`.

The original node no longer uses these as direct assembly steps:

- `lem-pur-sequence-site-completion-projection`.
- `def-weil-integral-derived-reduction`.
- `lem-pur-sequence-site-open-extension`.
- `prop-weil-pbc-proetale-constant-ring-map`.
- `lem-weil-l-adic-extension-integers-dvr`.
- `lem-sfb-integers-profinite-tower`.
- `lem-pur-coefficient-system-derived-comparison`.
- `def-compact-support-direct-image-detailed`.
- `lem-weil-pbc-exact-functor-derived-factorization`.
- `prop-pur-kinjective-resolutions-exist`.
- `lem-pc-right-derived-functor-triangulated`.
- `lem-weil-pbc-triangulated-functor-composite`.
- `lem-pur-system-pushforward-restriction-transition`.
- `lem-weil-proetale-direct-image-restriction-of-scalars`.
- `lem-pur-ringed-derived-pullback-linear`.
- `lem-pur-ringed-derived-pushforward-linear`.
- `lem-cbc-exact-linear-derived-functor`.
- `lem-weil-linear-abelian-derived-category`.

This list changes the parent proof route only. The geometric transition node still cites the system pushforward restriction-transition and normalized finite direct-image theorems. Other entries can remain reachable through existing definitions or other parents. The native varying-ring operations replace the separately planned open/system comparison imports; Mathlib exact descent, adjunction transfer and K-injective equivalences supply the triangulated and scalar calculations directly. The completed projection and quotient compatibility are proved here rather than assuming a fresh sequence-projection or scalar-linearity lemma.

## Where the brief, the DAG or earlier work was wrong

The generic declared system-pushforward transition theorem uses its semilinear-geometry presentation, whereas this construction uses native varying-ring operations. Applying it verbatim does not identify the constant-coefficient open/proper model normalizations. That geometric transport is the remaining lemma, not a failure of the source theorem. The existing CompactSupportSystemEvaluationCoherence theorem likewise uses a separately packaged slice presentation and does not directly identify this native evaluation.

The first server preflight found five newer textual consumers missing from the initial change-record snapshot. The refreshed record now has 522 rows, covering the current tools/downstream.py list, all current textual users and the earlier list. Each of the five reported users uses the unchanged quotient, level or transition declarations; no consumer adaptation is required.

No statement is disputed or weakened. The assigned node is not a realized unit step, and the unit route is retained. The old definitions and existing declaration statement were compared with the source; the moved definition block is verbatim. All consumers retain the same API, so no forced adaptation is included.

## New nodes

`def-weil-compact-support-reduction-tower-data`: attachment for the unchanged coefficient API, extracted solely to avoid an import cycle.

`def-weil-compact-support-native-system-evaluation`: constructed open and direct-image model comparisons, native coefficient levels, and the geometric evaluation isomorphism.

`lem-weil-compact-support-coefficient-transition`: constructed horizontal coefficient map and proved completed-restriction compatibility.

`lem-weil-compact-support-native-system-transition`: the remaining arbitrary-system geometric coefficient square, source step 4. It is a genuine geometric component, independent of reduction/scalar/existence construction.

Change record: `coord/changes/C4-compact-support-reduction-tower-native-construction.md`.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
