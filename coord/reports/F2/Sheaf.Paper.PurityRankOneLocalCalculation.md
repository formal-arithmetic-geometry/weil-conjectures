## What changed

The unchanged `WeilConjectures.PurityFiniteSetting.RankOne.rankOne_local_calculation` is
proved from the ordinary finite-coefficient calculation and a fully proved, generic acyclic-pair
localization theorem. Its proof constructs both normalized residues, proves their uniqueness,
transfers the normalization through the actual ordinary site-comparison map, and computes the
ideal-X valuations of polynomial quotients and Laurent monomials.

`PurityAcyclicPairSupportComparison` proves restriction-surjectivity for module injectives by
free-presheaf Yoneda, constructs the snake boundary on every injective resolution, proves the
support isomorphism and all other support vanishings, and proves the ordinary derived comparison
using localization and comparison acyclicity. Its supported degree-two isomorphism is the
conjugation requested by the existential Lean statement.

`PurityRankOneEtaleCalculation` proves the Laurent-unit description on the actual basic open,
Kummer additivity and the integer-power law, vanishing on powers, the scalar-root argument, the
coefficient map formula and the invertibility of the chosen exponent. Its ordinary cohomology
input combines the low-degree finite-module Kummer calculation with the proved higher-degree
vanishing on both affine curves. These inputs have no support, residue, valuation or pro-etale
conclusions. The higher-degree result holds for any coefficient sheaf annihilated by a positive
integer, not just the finite Tate line. `PurityFiniteLineZeroRestriction` proves degree-zero
restriction directly from the primitive-root trivialization and the actual constant sections
on the two connected schemes. The sole retained source hole is the degree-one Kummer computation.

`PurityFiniteModuleGenerator` proves the finite free presentation criterion.
`PurityTopDerivedRightExact` proves right exactness from successor vanishing.
`PurityKummerCoefficientGenerator` proves additivity and naturality of the actual coefficient
insertion and its finite-module extension. `PurityKummerTwistRightExact` proves finite-colimit
preservation by the actual twist construction. These complete the algebraic part of the retained coefficient argument.

`PurityRankOneSectionData` reexports the original canonical definitions with the same names and
values. Explicit comparison signatures, three irreducibility attributes and a local transparency
option prevent expansion of derived-functor data. The extraction permits the cohomology lemma
to refer to the original actual Kummer class without an import cycle. It was not a split to evade
the compiler limit. The main theorem's signature is textually unchanged. All thirteen extracted construction
bodies match the current shared source after whitespace normalization.

## Proved and sorry left

Original holes closed: `WeilConjectures.PurityFiniteSetting.RankOne.rankOne_local_calculation`
(node `thm-pur-rank-one-local-calculation`), 1 of 1. There is no sorry left in the item module.
The combining proof is complete. All twelve modules compiled together in import order
with `lcompile.py --all`, without warnings (`scratchpad/all-final6.log`).
The first full delivery dry run timed out in the main module. Profiling identified expensive
checking around the derived-comparison constructions; the main module now also enables
`backward.isDefEq.respectTransparency`, matching the data and helper modules. A profiled
compile completed in 25.5 seconds. The temporary profiler option was removed before delivery.
Also proved in this session:
`WeilConjectures.PurityFiniteSetting.RankOne.acyclic_pair_support_comparison` and
`WeilConjectures.PurityFiniteSetting.RankOne.rankOne_etale_calculation`,
`WeilConjectures.PurityFiniteSetting.RankOne.finite_line_high_cohomology`,
`WeilConjectures.PurityFiniteSetting.RankOne.finite_line_zero_restriction`, and
`WeilConjectures.PurityFiniteSetting.RankOne.finite_line_cohomology`, and
`ModuleCat.isIso_app_of_rankOne_of_finite`, and
`CategoryTheory.Functor.rightDerived_preservesFiniteColimits_of_succ_isZero`, and
`AlgebraicGeometry.Scheme.kummer_coefficient_generator_bijective`, and
`AlgebraicGeometry.Scheme.kummerModuleTwist_preservesFiniteColimits`, with their private
localization, comparison, Laurent-algebra and Kummer-law helpers.

Holes added: exactly one,
`WeilConjectures.PurityFiniteSetting.RankOne.finite_line_low_cohomology`
(node `lem-pur-finite-line-low-cohomology`, module `Sheaf.Paper.PurityFiniteLineLowCohomology`).
It is a public theorem with the finite free presentation proof in its docstring and
DAG record. It is strictly the degree-one ordinary-cohomology part of the source.
The degree-zero restriction is proved from primitive roots and constant sections. Higher-degree
vanishings are proved from the existing affine-curve cohomological-dimension theorem, with
explicit transfer to the actual derived evaluations. No definition or private
helper contains sorry. The work retained in that source lemma is the geometric transport
of the free computation to the affine-space model, the tensor/scalar-extension comparison
with the actual finite Tate line, and compatibility with the specified module-valued
Kummer class and A-action. The general finite-presentation and insertion arguments are
proved in the companion modules. This is a decomposition: the local declaration count is 1 closed minus 1 added = 0;
the delivery ledger separately measures the effect of pruning on the target closure,
not a claim that the target closure is sorry-free.

Unchanged direct consumers `RelativeSupportBottomDescent`, `PurityAffineLineOrientation`, and
`PurityAffineLineOrientationUniqueness` compile against the new facade (10.3, 16.6 and 5.0 s).
`ProjectiveBundleFormula` stops in its imports: the published build still has the retired
`Sheaf.AlgebraicGeometry.EtaleOpenCohomologyComparison` declaring
`AlgebraicGeometry.EtaleOpenComparison.restrictedSectionsEquiv`, also declared by the upstream
owner imported by the current source. The shared source has already removed the retired module
and already imports the upstream owner in the original item; this is a published-build mismatch,
not a consumer signature change. No consumer is adapted. Its exact diagnostic is retained in
`scratchpad/consumers-final1.log` for local audit.

## No longer needed

The direct proof imports of `RingedTopoiDerivedTensorPullback`,
`SupportComparisonPullbackCoherence`, `ComparisonGlobalCohomologyFiniteNormalized`,
`SupportComparisonBoundary` and `SupportSiteComparison` are removed. The actual ordinary
comparison is proved through `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`;
the supported map in this statement is constructed by conjugation. Thus the original planned
uses of `lem-pur-support-comparison-boundary`, `lem-pur-support-site-comparison` and
`lem-weil-pbc-comparison-global-cohomology` are not needed for this proof. Their modules may
remain reachable through other parts of the library; no claim of global unreachability is made.
The temporary recovery import of `FiniteEtaleDualizingNormalization` is also removed; coefficient
finiteness uses `Padic.finite_coefficientExtensionRing` directly.

`KummerAffineLine` and `RootsOfUnity.AlgebraicallyClosed` move to the degree-one source
result and remain needed. `AffinePuncturedLineAlgebra` moves to the ordinary calculation.
The direct `Sites.RootsOfUnity` import is redundant through the public data facade.
The twist helper also removes redundant direct imports of `ModuleCat.Monoidal.Closed` and
`Limits.FunctorCategory.Basic`, already supplied by its coefficient construction. The coefficient
generator keeps the cohomology map API as a proof import.
`Sites.ConstantSheafSections` is replaced by the proved module-valued constant-section
calculation in `Sites.ModulePointFunctions` for degree zero.

The exponent-change theorem `EtaleFiniteTwistPullback` is removed entirely from this
argument. The proved finite-module generator lemma extends the same-exponent free rank-one
calculation by finite free presentations. Higher vanishing makes degree-one cohomology right
exact, so neither a change of exponent nor induction on prime-order submodules is needed.
Thus `lem-asd-etale-finite-twist-pullback` is not used by this calculation. The proof still
performs the unit's coefficient extension and degree-zero/one computations.

The general pullback long-exact ladder and universal delta-functor imports are removed:
the retained coefficient argument uses the proved ordinary derived long exact sequence
and its finite-colimit criterion, together with the Ext maps in `SheafCohomology.Basic`. Thus
`lem-weil-pbc-pullback-cohomology-long-exact-ladder` and
`lem-weil-pbc-right-derived-universal-delta-functor`, together with their site-size and
enough-injectives prerequisites for that argument, are not needed by this calculation.
`Sites.Kummer` is available through the public data imports, so its redundant direct import is
removed. The original public imports are preserved through the public data facade, retaining the
upstream WeilConjectures comparison owners already used by the current shared source. The DAG of the main
node now names only the two actual proof inputs; the new nodes retain their own dependencies.

The following 102 source modules leave this item's import closure, comparing the
shared source imports with this packet. Other targets may still import them. The table also
lists their attached DAG nodes; an em dash means no direct Lean attachment was found.

| Module no longer reached from this item | Attached nodes |
| --- | --- |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteGlobalPresentationInternalHomColimit` | `lem-weil-pbc-finite-global-presentation-internal-hom-colimit` |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteFinitePresentationInternalHomColimit` | `lem-weil-pbc-site-finite-presentation-internal-hom-colimit` |
| `Sheaf.AlgebraicGeometry.AffineClosedSpecializationLocalization` | `lem-weil-pbc-affine-closed-specialization-localization` |
| `Sheaf.AlgebraicGeometry.ClosedImmersionProducts` | `lem-weil-pbc-closed-immersion-products` |
| `Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized` | `lem-weil-pbc-comparison-global-cohomology` |
| `Sheaf.AlgebraicGeometry.ComparisonPullbackOpenUnit` | `lem-pur-comparison-pullback-open-unit` |
| `Sheaf.AlgebraicGeometry.DerivedSupportDirectImageComparison` | `lem-pur-derived-support-comparison-direct-image` |
| `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence` | `lem-cbc-extension-zero-composition` |
| `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCompCanonical` | `lem-cbc-extension-zero-composition-canonical-comparison` |
| `Sheaf.AlgebraicGeometry.EtaleConstantModuleFlat` | `lem-pur-etale-constant-module-flat` |
| `Sheaf.AlgebraicGeometry.EtaleConstantModuleTensor` | `lem-pur-etale-constant-module-tensor` |
| `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear` | `lem-weil-pbc-inverse-image-composition-module-linear` |
| `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinearCore` | `lem-weil-pbc-inverse-image-composition-module-linear-core` |
| `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives` | `lem-weil-pbc-module-sheaves-enough-injectives` |
| `Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat` | `lem-pur-etale-sum-flat-kflat`, `lem-pur-etale-sum-flat-terms-aux` |
| `Sheaf.AlgebraicGeometry.EtaleSumPreservesFlat` | `lem-pur-etale-sum-flat-aux` |
| `Sheaf.AlgebraicGeometry.EtaleSumPreservesKFlat` | `lem-pur-etale-sum-kflat-aux` |
| `Sheaf.AlgebraicGeometry.EtaleSumTensorTestComparison` | `lem-pur-etale-sum-tensor-test` |
| `Sheaf.AlgebraicGeometry.EtaleSumTensorTestProjection` | `lem-pur-etale-sum-tensor-test-projection` |
| `Sheaf.AlgebraicGeometry.EtaleSupportedSections` | `def-pur-etale-derived-supported-sections` |
| `Sheaf.AlgebraicGeometry.NormalizedSupportTriangle` | `lem-pur-support-restriction-triangle` |
| `Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization` | `lem-sf-open-comparison-unit-normalization` |
| `Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedCounit` | `lem-weil-pbc-proetale-abelian-closed-counit` |
| `Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport` | `lem-weil-pbc-proetale-abelian-closed-support` |
| `Sheaf.AlgebraicGeometry.ProEtaleClosedAbelianFilteredColimits` | `lem-weil-pbc-proetale-closed-abelian-filtered-colimits` |
| `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange` | `lem-trf-open-square-exchange` |
| `Sheaf.AlgebraicGeometry.ProEtaleExtensionByZero` | — |
| `Sheaf.AlgebraicGeometry.ProEtaleExtensionByZeroAdjunction` | — |
| `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison` | `lem-cbc-proetale-extension-zero-comparison` |
| `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact` | `lem-weil-extension-by-zero-exact` |
| `Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison` | `new-lem-weil-pbc-proetale-module-inverse-image-unit-comparison` |
| `Sheaf.AlgebraicGeometry.ProEtaleModuleSpecializationUnit` | `lem-weil-pbc-proetale-module-specialization-unit` |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf` | `det-sf-open-closed-sequence-ring-sheaf` |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange` | — |
| `Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives` | `lem-weil-pbc-proetale-restriction-injectives` |
| `Sheaf.AlgebraicGeometry.ProEtaleRingSheafBaseChangeMates` | `lem-sf-ring-sheaf-base-change-mates` |
| `Sheaf.AlgebraicGeometry.ProEtaleRingSheafClosedLocalization` | `lem-sf-ring-sheaf-closed-localization` |
| `Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations` | `def-sf-proetale-ring-sheaf-operations` |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedCounit` | `lem-weil-pbc-proetale-ringed-closed-counit` |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedFilteredColimits` | `lem-weil-pbc-proetale-ringed-filtered-colimits` |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedLocalizationSequence` | `lem-weil-pbc-proetale-ringed-localization-sequence` |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` | `lem-weil-pbc-proetale-ringed-open-closed` |
| `Sheaf.AlgebraicGeometry.ProEtaleSpecializationAffineCoordinates` | `new-lem-weil-pbc-specialization-affine-coordinates` |
| `Sheaf.AlgebraicGeometry.ProEtaleSpecializationCounit` | `new-lem-weil-pbc-specialization-closed-site-counit` |
| `Sheaf.AlgebraicGeometry.ProEtaleSpecializationRestrictionSections` | `lem-weil-pbc-proetale-specialization-restriction-sections` |
| `Sheaf.AlgebraicGeometry.ProEtaleSpecializationUnitComparison` | `new-lem-weil-pbc-specialization-unit-comparison` |
| `Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct` | `def-pur-proetale-supported-exterior-product` |
| `Sheaf.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus` | `lem-weil-pbc-proetale-qcqs-fp-section-calculus` |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | `lem-pur-support-comparison-boundary` |
| `Sheaf.AlgebraicGeometry.SupportQuotientFlat` | `lem-pur-support-quotient-flat` |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | `lem-pur-support-quotient-product` |
| `Sheaf.AlgebraicGeometry.SupportRestrictionTriangle` | — |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | `def-pur-support-comparison-unit`, `lem-pur-support-site-comparison` |
| `Sheaf.AlgebraicGeometry.SupportedExteriorProduct` | `def-pur-supported-exterior-product` |
| `Sheaf.AlgebraicGeometry.SupportedProductQuotientModel` | `lem-pur-supported-product-quotient-model` |
| `Sheaf.CategoryTheory.CochainCoefficientUniverseTransport` | `def-pur-cochain-coefficient-universe-transport` |
| `Sheaf.CategoryTheory.ModuleInverseImageUnitComparison` | `lem-weil-pbc-module-inverse-image-unit-comparison` |
| `Sheaf.CategoryTheory.SiteConstantModuleHom` | `lem-pur-site-constant-module-hom` |
| `Sheaf.Paper.EtaleSumTensorTotalization` | `lem-pur-etale-sum-tensor-totalization` |
| `Sheaf.Paper.PurityComparisonUnitInjectiveModel` | `lem-pur-comparison-unit-injective-model` |
| `Sheaf.RingTheory.BoundedWContractibleExtension` | `lem-weil-pbc-wcontractible-ring-extension` |
| `Sheaf.RingTheory.EtaleContraction` | `def-weil-pbc-etale-contraction` |
| `Sheaf.RingTheory.EtaleContractionProperties` | `lem-weil-pbc-etale-contraction` |
| `Sheaf.RingTheory.EtaleContractionSize` | `lem-weil-pbc-etale-contraction-size` |
| `Sheaf.RingTheory.FactorsThroughLocalization` | `lem-factors-through-localization-of-smooth` |
| `Sheaf.RingTheory.IndPrincipalZariskiOfLocalRingIso` | `lem-weil-pbc-local-rings-ind-zariski` |
| `Sheaf.RingTheory.PrincipalWLocalization` | `def-weil-pbc-w-localization` |
| `Sheaf.RingTheory.PrincipalWLocalizationEvaluation` | `lem-weil-pbc-principal-w-localization-evaluation` |
| `Sheaf.RingTheory.PrincipalWLocalizationPoints` | `lem-weil-pbc-w-localization-points` |
| `Sheaf.RingTheory.PrincipalWLocalizationPrimeCharts` | `lem-weil-pbc-principal-w-localization-prime-charts` |
| `Sheaf.RingTheory.PrincipalWLocalizationSize` | `lem-weil-pbc-principal-w-localization-size` |
| `Sheaf.RingTheory.ProfiniteComponentRingPullback` | `lem-weil-pbc-profinite-component-ring-pullback` |
| `Sheaf.RingTheory.RetainedLocalization` | `def-weil-pbc-retained-localization` |
| `Sheaf.RingTheory.RetainedLocalizationProperties` | `lem-weil-pbc-retained-localization` |
| `Sheaf.RingTheory.RetainedLocalizationSize` | `lem-weil-pbc-retained-localization-size` |
| `Sheaf.RingTheory.StrictWCover` | `def-weil-pbc-strict-w-cover` |
| `Sheaf.RingTheory.StrictWCoverProperties` | `lem-weil-pbc-strict-w-cover` |
| `Sheaf.RingTheory.StrictWCoverSize` | `lem-weil-pbc-strict-w-cover-size` |
| `Sheaf.RingTheory.WContractibleClosedLocalization` | `lem-weil-pbc-wcontractible-closed-localization` |
| `Sheaf.SecSmoothPurity.CochainCoefficientArrows` | `def-pur-cochain-coefficient-arrows` |
| `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence` | `lem-pur-cochain-pullback-tensor-coherence` |
| `Sheaf.SecSmoothPurity.CochainTensorCoherenceData` | `def-pur-cochain-tensor-coherence-data` |
| `Sheaf.SixFunctors.IntrinsicDerivedTensor` | — |
| `Sheaf.SixFunctors.OpenClosedFlatness` | `lem-sfb-open-closed-flatness` |
| `Sheaf.SixFunctors.ProEtaleIntrinsicTensorComparison` | `lem-sfb-proetale-intrinsic-tensor-comparison` |
| `Sheaf.Topology.BoundedExtremallyDisconnectedCover` | `lem-weil-pbc-bounded-extremally-disconnected-cover` |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.KummerCover` | — |
| `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula` | `def-sfb-adjunction-has-projection-formula`, `def-sfb-adjunction-projection-formula`, `def-sfb-projection-formula` |
| `WeilConjectures.CategoryTheory.Sites.EquivariantEvaluation` | — |
| `WeilConjectures.FieldTheory.KummerFreeSubgroup` | — |
| `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective` | — |
| `WeilConjectures.Mathlib.GroupTheory.GroupAction.Quotient` | — |
| `WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms` | — |
| `WeilConjectures.Mathlib.RingTheory.Algebraic.Basic` | — |
| `WeilConjectures.Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` | — |
| `WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSite` | — |
| `WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits` | — |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExternalProduct` | — |
| `WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation` | — |
| `WeilConjectures.SixFunctors.ProEtale.GenericPoint` | — |
| `WeilConjectures.SixFunctors.ProEtale.KummerCover` | — |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs` | `def-sfb-module-linear-open-lower-shriek`, `def-sfb-module-lower-shriek`, `def-sfb-module-open-lower-shriek`, `def-sfb-module-open-lower-shriek-adjunction`, `sk-def-sfb-module-lower-shriek` |

## Where the brief, the DAG or earlier work was wrong

The first server preflight rejected the new records because LeanFinder and Loogle were
incorrectly counted as different search kinds. Eleven additional successful LeanSearch queries
now complete the required LeanSearch, Loogle/LeanFinder, and Mathlib-source grep records.

`KummerAffineLine.kummer_affine_line` states the free-coefficient computation only. The finite
quotient in the item need not be free over Z/ell^N for the arbitrary N in its statement. The
separate finite-module result therefore requires coefficient extension. The finite free
presentation argument supplies a shorter route than prime-order devissage: only the free
rank-one computation is needed, together with right exactness from the proved H2 vanishing.
No freeness hypothesis is added and no statement is weakened.

The previous retained support lemma still had a hole; this session proves it. Its old proof
prose claimed identification with an independently specified supported comparison, although its
Lean statement only asks for an existential supported isomorphism. The prose and DAG now match
the implemented conjugation and the exact stated conclusion. The snake boundaries themselves
are still the specified actual boundaries on every resolution, with their sign fixed.

The current shared source already retired the two old Sheaf comparison imports in favour
of their upstream owners; this packet is synchronized with that change. Repeated
provider interruptions left no delivery in progress. The recovery file records attempts beginning
2026-10-19 00:57 UTC; the current launcher budget start is 2026-10-19 17:07:48 UTC, reset on a
resume. The budget files were not edited. This metadata reset does not supply any proof and is
not used to claim a net decrease in holes.

## New nodes

`def-pur-rank-one-section-data` records the unchanged canonical data extracted to break the
cohomology/ordinary-calculation import cycle; it adds no hole.

`lem-pur-finite-line-cohomology` combines the degree-one calculation, the proved degree-zero
restriction, and higher vanishing, with an explicit split of positive degrees into one and at
least two. It adds no hole.

`lem-pur-finite-line-high-cohomology` proves the higher vanishings for any torsion module-valued
sheaf on these curves. It uses the existing affine-curve theorem and the actual module/abelian,
evaluation/Ext and open-site comparisons. It adds no hole.

`lem-pur-finite-line-zero-restriction` proves the degree-zero calculation by a primitive-root
trivialization, actual constant sections, and the natural zeroth-derived comparison. It adds
no hole and requires neither finiteness of A nor N≥1.

`lem-pur-finite-line-low-cohomology` records the separate degree-one finite-module calculation
of the unit's Coefficients and Degrees 0 and 1 proof. It adds one hole. The zero coefficient ring,
N=1, ramified quotients and arbitrarily large annihilating N are included. Its shorter proof
plan uses finite free presentations at the same exponent, never unsupported freeness.

`lem-pur-finite-module-generator` proves the finite-presentation algebra step by adapting the
existing upstream coproduct/cokernel proof from arbitrary colimits to finite colimits. Finiteness
of the coefficient ring makes the free kernel presentation finite. It adds no hole.

`lem-pur-top-derived-right-exact` proves finite-colimit preservation for an additive left-exact
functor in its top potentially nonzero right-derived degree, using the proved long exact
sequence and Mathlib’s right-exactness criterion. It adds no hole.

`lem-pur-kummer-coefficient-generator` proves additivity and naturality of the actual
coefficient insertion, constructs its cohomology natural transformation, and extends
bijectivity from the residue ring to every finite module. It adds no hole.

`lem-pur-kummer-twist-right-exact` proves finite-colimit preservation by the actual Kummer
module twist using pointwise tensor colimits and the sheafification adjunction. It adds no hole.

`lem-pur-rank-one-etale-calculation` combines that calculation with the proved actual coefficient
map, unit algebra and Kummer laws; it adds no hole.

`lem-pur-acyclic-pair-support-comparison` is the proved generic localization and site-comparison
argument for an acyclic open pair; it adds no hole. It needs no Kummer generator.

Change record: `coord/changes/F2-rank-one-section-data.md`. No other group's module is adapted.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
