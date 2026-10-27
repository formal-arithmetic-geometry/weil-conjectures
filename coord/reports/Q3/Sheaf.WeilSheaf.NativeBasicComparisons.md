## What changed

Proved `AlgebraicGeometry.nativeWeilBasicComparisons` with its statement unchanged.
Added one fully proved private helper, `nativeOpenAdjunction`, using the existing source
adjoint-triple lifting theorem and the actual Frobenius compatibility lemmas.
Direct-image composition and identity use existing native source APIs. Open extension
preserves boundedness by exactness and constructibility degree by degree. Successive and
identity open extensions are identified by uniqueness of left adjoints, then descended to
the ordinary unbounded derived categories. The DAG proof now records this shorter route.
No public definition, signature, attribute or public import changed; no consumer adaptations.

Validation: the item compiled cleanly through lcompile.py in 8.2 seconds. The original
hypotheses and universes are unchanged. Identity maps, empty schemes and zero complexes
are included: the proof uses functorial adjunction and exactness APIs without nonempty
or positive-rank assumptions. No quasi-compactness of the schemes or absolute separatedness
was introduced. The unit's own statement and realized steps are unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.nativeWeilBasicComparisons`
(node `lem-sf-native-weil-basic-comparisons`).
Added 0 holes; split off 0 statements. There are no remaining sorries in the item or packet.
The private adjunction helper is fully proved. This is a proof, not a decomposition.
Imported source declarations retain their existing dependency and axiom status; delivery
preflight performs the project's declaration and axiom checks.

## No longer needed

Removed these private imports from this item:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientGeneralPullbackIso`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.RingedSheafSliceAdjunction`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Yoneda`
- `Sheaf.CategoryTheory.ExactDerivedComposition`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`

These original proof dependencies are unnecessary for this proof:

- `def-weil-size-convention`
- `lem-sf-twisted-action-ringed-site`
- `prop-pur-kinjective-resolutions-exist`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-continuous-coefficient-general-pullback-isIso`
- `def-weil-proetale-inverse-image`
- `lem-weil-pbc-ringed-topoi-module-adjunction`
- `lem-weil-pbc-site-pullback-abelian-exact`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `lem-weil-pbc-kinjective-total-derived`
- `def-sfb-right-derived-functor`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-weil-pbc-ringed-sheaf-slice-adjunction`
- `lem-sf-native-weil-open-exact-constructible`
- `lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection`

Their constructions are superseded here by existing proved source-library APIs: native
K-injective pushforward composition, exact open extension and its constructibility theorem.
The separate `NativeWeilOpenExactConstructible` statement is unnecessary here because
`WeilSheaf.isAdicConstructibleSheaf_extensionByZero` already supplies precisely the needed
sheaf property and the source instances supply exactness. The generic coefficient-colimit,
site-localization and resolution developments need not be reconstructed by this item.
All obsolete top-level tool_uses entries were removed while retaining the order of survivors.
No modules or declarations are withdrawn. These pruning statements concern this item's
proof edges; other consumers and the adopted source tree keep all their declarations.
The retained exact-derived nodes describe the existing source descent APIs used here.
The source adjoint-triple lift is a proved specialization of the fixed-pair lifting step,
with all of its compatibility hypotheses discharged by existing source lemmas.

## Where the brief, the DAG or earlier work was wrong

The DAG plan reconstructed substantial native categorical infrastructure already available
in the adopted source library. In particular, the source has the direct-image composition,
exactness and constructibility results. Only the open-comparison assembly was absent as a
ready-made native API; it is proved here via existing adjunction lifting and uniqueness.
No mathematical statement was changed or disputed, and no source-library signature or
non-theorem body was edited. No new nodes or change records are required.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
