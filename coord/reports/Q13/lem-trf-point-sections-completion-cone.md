## Worker report

The module `Sheaf.Paper.PointSectionsCompletionCone` states the sectionwise completion-cone comparison with the specified whole-derived-object isomorphisms, both strict cone coordinates, quasi-isomorphism invariance, every good representative, and naturality for every derived morphism. The theorem proofs are `sorry`; all definition data are actual compositions or choices determined by a unique normalization. No statement correction or dependency-interface repair is needed.

Hypothesis and clause correspondence:

- The finite-field datum p,a,q,k₀,k is `D : FiniteFieldDatum.{u}`; its finite-base, algebraic-closure and characteristic data are inherited from that recorded structure. `l : ℕ`, `[Fact l.Prime]`, `[Fact (l ≠ D.p)]` give the coefficient-prime conditions. `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` give the finite extension. The existing coefficient-extension definitions specify its valuation ring, uniformizer, and all positive quotients. No auxiliary scheme X₀ or a single finite level is required for this point statement, so the entire finite-level conventions structure is not imposed as an extra hypothesis.
- The point is `Spec (.of D.k)` on `Scheme.ProEt.topology`. `frobenius D` is Spec of the existing `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k`, with the finite enumeration supplied by `Fintype.ofFinite`. This is g on the point, rather than the base-changed automorphism on an unrelated fibre product.
- The completed sheaf R and module category are the recorded `completedIntegralCommRingSheafUnrestricted` and `integralTowerModules`. `sections` aliases `CompletedStalk.sectionsComplex`, i.e. termwise `pointIntegralSections`. This is actual final-object evaluation with the canonical integral scalar action, obtained by restriction along `pointIntegralSectionMap`; it does not replace the completed coefficient sheaf by a discrete constant sheaf. The target is the library's `ModuleCat` over the common `ULift` of O_E, as in the recorded point fibre. It retains exactly the same section elements and maps. The canonical constant-section identification Γ(s,R)=O_E is the one used by that point-fibre interface; no arbitrary ring equivalence is selected.
- An arbitrary strict tower is `T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules ...) ℤ`. `integralOperationsTowerStep T n` is its actual transition. `integralOperationsRoos T` is the existing mapping cocone of `towerTransitionEndomorphism`, hence Cone(1-s)[-1] with the node's signed differential. Its coordinate order is accessed by the existing `CompletedStalk.roosSecond` (shifted b) and `CompletedStalk.roosFirst` (unshifted a), avoiding a second cone convention.
- The specified c_T is the existing `CompletedStalk.sectionsRoos D l E T`, uniquely fixed by its two coordinate equations. The first conjunct of `pointSectionsCompletionCone` explicitly states BOTH coordinate equations. Each is the sectionwise product identification, tested against every degree and every product projection. Thus the comparison is a chain isomorphism, with no arbitrary triangle filler.
- The next two conjuncts give c_U ΓH(w)=H(Γw)c_T and the diagonal formula for H(w) on BOTH coordinates. The existing `integralOperationsRoosMap` is the product map on both shifted-cone summands; the equations against every projection state its coordinate formula explicitly.
- The first conjunct also states `integralOperationsDerivedLimitProperty` for the whole sheaf tower and `ModuleDerivedLimit` for the whole section tower. The latter wraps the recorded `IsDerivedLimit` with existence of the required product, using the same small-Hom localization as the point fibre. The product witness is ordinary existence, not a choice of comparison. No boundedness or Mittag--Leffler condition is imposed on these towers.
- The levelwise-quasi-isomorphism conjunct says that both H(w) and H(Γw) are quasi-isomorphisms. Together with the preceding strict naturality equality this gives descent of c through every inverted arrow: its square can be multiplied by the two inverses, and then composed for every roof. This statement retains precisely the entire-tower localization, not a per-degree substitute.
- `N : sfIntegralConstructibleCategory ...` is exactly derived complete with constructible reductions in one common finite interval. `P : (integralOperationsGoodComplex ...).FullSubcategory` is exactly K-flat with flat terms, without boundedness. `q : DerivedCategory.Q.obj P.obj ≅ N.obj` permits EVERY localized resolution comparison (in particular every quasi-isomorphism P→a representative of N), rather than one chosen resolution. No stronger Tor-amplitude assumption appears.
- `reductions` is the recorded `integralScalarTowerFunctor` at the identity field extension: its levels are Res_n(P tensor (A_n)_s), with actual quotient transitions. `integralOperationsPullbackTowerFunctor ... (frobenius D)` gives exactly C_n=Res_n g_n*P_n with its actual transitions. Composing either strict tower with `sections` gives D and B. Index n in Lean means the positive exponent n+1, so exponent one is included.
- `completionModel` composes the normalized identity-extension model comparison, the exact-sections localization comparison `factors`, and Q(c_P). `completionModelAt` transports it through q. `completionComparison_existsUnique` asserts the natural isomorphism on the entire constructible category whose `CompletionNormalization` equation identifies its value, on EVERY q, with the specified completion augmentation. This is alpha before identifying its target with each strict cone; `alpha` makes that final identification.
- `augmentation` is sections of `completedScalarIdentityUnit` followed by c_P. The explicit augmentation conjunct of the main theorem gives its unshifted projection as `integralScalarTensorSection ... 1 z` at the final object for every n and degree, and its shifted projection as ZERO. The next conjunct is exactly alpha_N Γ(q)=Q(a_P), with `factors` accounting for localization versus termwise sections.
- `pullbackModel` uses `integralDerivedPullbackComparison`, `factors`, and Q(c_C) in that order. `beta` transports it along q. Hence beta has exactly the node's defining representative comparison and the identity sectionwise product maps on BOTH coordinates, without a new existence choice. Its target is the Roos complex on B. The general derived-limit conjunct identifies both special targets with their Rlim descriptions.
- `reductionMap` and `pullbackMap` use the separately existing descended functors and THEIR model comparisons; neither is defined by alpha. The strict-map computation conjunct states that these induced maps equal the localized diagonal Roos maps whenever w represents f. `DerivedNaturality` then quantifies arbitrary derived morphisms f and arbitrary P,P',q,q', and gives precisely H(D(f)) alpha=alpha' Γ(f), and H(B(f)) beta=beta' Γ(Lg*f). Taking f to be identity and arbitrary q,q' is the asserted independence of resolutions under those specified derived comparison maps. No condition asks the morphism to be a single chain map between the initially selected resolutions.

Dependency declarations read and used:

- `Sheaf.Paper.IntegralOperationsWellDefined`: `integralOperationsGoodComplex`, `integralOperationsTowerStep`, `integralOperationsRoos`, `integralOperationsRoosMap`, `integralOperationsRoosFunctor`, `integralOperationsPullbackTowerFunctor`, `integralOperationsDerivedLimitProperty`, and the normalized descent `integralOperationsWellDefined`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`, `sfIntegralConstructibleCategory`, incorporating `IsSfDerivedComplete`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: `CochainComplex.IsKFlatIndependentCoefficients`; `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`, as incorporated by the recorded good-complex predicate.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`: `completedScalarIdentityUnit`, its unique two-coordinate normalization, `completedScalarComparison` and `finiteFreeCompletedScalarComparison`. Their identity-extension representative is the recorded `integralScalarTowerFunctor`, `integralScalarExtensionOfUniverses`, `integralScalarExtensionComparisonOfUniverses`.
- `Sheaf.Paper.DerivedPullbackTensorHom` reexports `integralDerivedPullback` and its normalized `integralDerivedPullbackComparison`; these are the actual ambient operations whose restriction it defines. The finite levels use the recorded `integralOperationsLevelPullback`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: actual completion and projection constructions, with original small-site universe. `Sheaf.Paper.AdicCoefficientDatum`: the same positive coefficient quotients and canonical transition convention. `Sheaf.Paper.InverseImagePullbackComparisonDerived`: its specified integral cone representative, not an arbitrary map.
- `Sheaf.Paper.PointProEtaleSectionsExact`: `pointModuleSections`, `point_proEtale_sections_exact`; `FiniteCoefficientPoint` supplies `pointFibreIntegralAmbient`, `pointFibreIntegralLimits`, `pointFibreIntegralColimits`, with the canonical scalar restriction from `CompletedIntegralCoefficientGerm`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed` uses and reexports `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic`; `TraceFormulaCoefficientConventions` supplies the coefficient conventions. `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`: `IsDerivedLimit`. Proof-plan imports include exact products, strict Roos comparison and model, derived-limit-products-core, derived change of rings cochain model. They are plain imports when only the proof uses them.
- Added def-trf-point-sections-roos-comparison to stmt_deps. Its existing record owns the six helpers sectionsComplex, moduleQ, roosFirst, roosSecond, sectionsRoos_existsUnique, sectionsRoos in the unchanged Sheaf.Paper.CompletedStalkReparametrizationCoherence module. sectionsRoos is chosen from the locally stated unique normalization, and does not use CompletedStalk.coherence. The theorem node is no longer added as a statement dependency.

Edge cases checked before and during transcription:

- Zero complexes and zero tower maps: both coordinates and all augmentations vanish.
- The first quotient has exponent one; there is no accidental exponent-zero quotient.
- Arbitrary negative cochain degrees are allowed. The shifted coordinate is degree i-1; its normalization is zero on the augmentation, with the dependency's signed mapping-cocone convention.
- Constant towers, zero transitions, and unbounded towers are included: only exact countable products are used for the general cone assertion. No surjectivity of transitions is required.
- A torsion constructible input need not be termwise flat or have finite Tor dimension. Only its resolution P is K-flat with flat terms, as in the node.
- Every representative isomorphism q is admitted, and identity derived morphisms compare any two such choices. The equality fixes whole morphisms, avoiding detection by finite projections alone.
- The small pro-etale site retains object universe u+1 and morphism universe u; coefficients/modules are in u+1. No equality of site universes is imposed. `ULift` is the existing coefficient-size convention.

Searches (all performed with the prescribed search wrapper and direct source searches):

- LeanFinder: “Exact sections of completed sheaf complexes commute with the normalized shifted cone inverse limit and completion augmentation”. Eight hits, including site evaluation cone lemmas and mappingCone lift formulas; no theorem contains the specified completion and pullback comparisons.
- Loogle: `CategoryTheory.Limits.evaluationPreservesLimits`. One hit, ordinary evaluation preserving limits, not the derived complete-coefficient comparison.
- LeanSearch: “exact global sections commute with the homotopy inverse limit of a tower of module sheaves”. Eight hits, including global sections, sheaf limit existence and module sections; no normalized derived comparison theorem.
- msearch grep: `Roos|derived.*complet|mappingCocone.*[Ee]val|[Ee]val.*mappingCocone`: zero hits.
- Direct rg in Mathlib, WeilConjectures, and Sheaf: `PointSectionsCompletion|pointSectionsCompletion|point.sections.completion|sections.*[Rr]oos|[Rr]oos.*[Ss]ections`, plus the exact item id in WeilConjectures. Found CompletedStalk.sectionsRoos (reused) and the downstream LocalFrobeniusTransportNormalization specialization. The latter depends through the integral-point-transport node on this item and is therefore NOT imported. No existing declaration states the full item. Additional name-clash search for `pointSectionsCompletionCone|CompletionNormalization|ModuleDerivedLimit` found only a separately namespaced completion section.

Validation: prescribed scompile.py checked the module both as a sandbox module and under its final module name. The preliminary finite-enumeration issue and an explicit dependent shift-additivity instance were repaired; the unused variable was renamed `_n`. Final compilation is repeated by the dry-run wrapper. Every theorem in this delivery has only `sorry` as proof.

There is one new definition ownership node reusing existing declarations, no disputed statement, and no changes to the original mathematical statement or proof plan.


## New nodes

def-trf-point-sections-roos-comparison records the existing termwise sections functor,
ordinary-module localization, both Roos coordinate projections, the unique normalized
comparison lemma, and its chosen isomorphism. Its source is clause (3) of the current
blueprint's prop-trf-rational-frobenius-integral-model.proof.md, specifically the
sectionwise cone identification used in this item's completion comparisons. In the
notation of the new node, sectionsComplex is Γ in every degree; moduleQ is the
existing small-Hom localization over the common coefficient lift; roosFirst projects
to degree i of level n, and roosSecond projects to degree i-1. The two equations in
sectionsRoos_existsUnique are exactly the two displayed normalization equations, and
sectionsRoos is its .exists.choose. Thus the proof used to select the data determines
that data uniquely. The same general projection declarations apply in every abelian
category with countable products; the comparison specializes to the fixed point and
completed coefficient sheaf. No boundedness or transition-surjectivity assumption is
introduced, and zero towers and every integer cochain degree are included.

The three new wrapper searches are recorded by tool/query in this node's
mathlib_searches, with the actual hit counts and declaration names from searches.jsonl.
LeanSearch returned global sections and mapping-cone tools; LeanFinder returned product
extensionality for sheaf equalizers; Mathlib grep returned zero exact-name hits. Direct
rg of WeilConjectures and Sheaf located the exact six existing declarations above;
blueprint_refs search returned zero matching blueprint nodes. The coherence theorem's
node lists these as local helpers but does not define their notion in its statement.
This new node gives those notions an explicit definition owner, as the return requested;
its existing: true record introduces no Lean module and duplicates no definition.

## Repair of maintainer return H2

The immutable returned delivery f33cf8e17229 added
lem-trf-completed-stalk-reparametrization-coherence merely to access definitions in its
module. Replaced that addition with the new definition node above, including exactly
sectionsComplex/moduleQ/roosFirst/roosSecond/sectionsRoos_existsUnique/sectionsRoos in
lean.declarations. The existing module and this delivery's Lean file are unchanged.
The item's statement and proof fields remain identical to current main; only its
lean and the authorized added statement dependency differ. The first saved-packet
dry run passed mechanically, but the independent H2 ownership correction was still
required and is now explicitly represented in the DAG. No independent second agent
was started, in accordance with the dispatcher's instruction; the maintainer supplies
the independent review.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
