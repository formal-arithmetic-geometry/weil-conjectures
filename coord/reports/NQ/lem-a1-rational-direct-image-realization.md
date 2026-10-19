## Worker report

Module: `Sheaf.Paper.RationalDirectImageRealization`. Primary declaration:
`AlgebraicGeometry.Scheme.ContinuousRational.DirectImage.rational_direct_image_realization`.
The node's statement is unchanged. There are no new DAG nodes or dependency repairs.

The conclusion supplies one compatible realization family `r : ContinuousRational.Family l`
and a `DirectImage.Package k l r`. All auxiliary structures unpack this node's own
comparison obligation. Definitions contain actual data. The only postponed proofs are
`modulePush_additive` (the additive property required for the actual right-derived
construction) and the primary theorem. Both have source and proof docstrings.

Hypothesis and clause check:

| Node clause | Lean rendering |
| --- | --- |
| Field k, prime l invertible in k | `(k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : k))` in the primary theorem. |
| Separated finite-type k-schemes X,Y and k-morphism f | `Space k l` stores the scheme, its `Over (Spec (.of k))`, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` instances. `Package.along` quantifies every pair and every `f` with `[f.IsOver (Spec (.of k))]`. |
| Noetherian, finite-dimensional, l-coprime scheme consequences | `Space` extends the dependency's `Base l`. Its noetherian, dimension-bound and stalk-unit proofs are redundant consequences of finite type over k and `_hl`, exactly as proof step 1 states. No smoothness, properness, nonemptiness or algebraic-closedness condition is imposed. |
| Every finite E/Q_l, valuation ring and uniformizer | `Package` quantifies `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. It reuses `pbcIntegralDatum l E` and `pbcUniformizer l E`, including their prescribed ULift of the integers into the site coefficient universe. |
| B_T as the completed finite quotient coefficient sheaf, E_T as its localization and J_T(QK)=E_T tensor^L K | The given `r.realization E T : At l E T` supplies `integralIso`, `localizationIso`, `inclusion`, their finite-quotient/constant-section normalizations, `J`, and the integral derived-tensor comparison. These are not replaced. |
| Raw rationalization, without a Karoubi envelope | `rawPush` uses `pbcConditionalRational` and hence `ScalarLocalization.transport`; all domains are the published `PbcRationalCategory`. |
| Integral constructibility, including compatible étale origins | `Comparison.preserves` is precisely `PbcIsBoundedConstructibleComplete` of the ordinary derived pushforward of every object of `PbcBoundedConstructibleComplete`. Its three-clause predicate includes intrinsic completeness, uniform constructible reductions, and compatible origins. |
| Ordinary B-derived direct image, canonically identifiable with the strict reduction tower | The operation is `pbcActualDerivedPush`, the already published ordinary completed-ring right derived functor. `CompletedDirectImageLimits` supplies its unit-normalized strict tower comparison. `SfIntegralDirectImageConstructible` supplies finiteness through the dependency's integral characterization. No unrelated tower limit or arbitrary direct-image functor is substituted. |
| Ordinary ambient continuous E-module right derived direct image | `modulePush f c` is `SheafOfModules.pushforward` with the ring map adjunct to the continuous coefficient structural map `c`; `derivedPush` is exactly its `rightDerivedFunctor`, using K-injectives in all modules. There is no discrete non-torsion étale coefficient category. |
| The canonical localization projection | `projection` is the explicit adjoint transpose of the specified `Along.ambient` balanced pullback map followed by scalar extension of the actual ordinary B-counit. This is the normalized projection mate from proof steps 7 and 11, not an arbitrary morphism. |
| Isomorphism for every integral constructible K | `Comparison.projection_iso` quantifies every integral K and asserts `IsIso (projection ... K.obj)`. |
| Natural isomorphism J_Y Rf_rat -> Rf_E J_X, with the same integral components | `Comparison.comparison` is a natural isomorphism of the actual functors. `integral_normalization` equates its component on QK with `projection`, conjugated only by the existing `At.integral` comparisons. |
| Actual ordinary continuous adjunction | `Ordinary.moduleAdjunction` has the sectionwise tensor-unit equation `unit_sections`. `Ordinary.adjunction` has `transpose`, using the published pullback counit and the actual right-derived unit `pushUnit` on all cochain representatives. Thus it is fixed by the ordinary derived adjunction, not a new arbitrary adjunction. |
| Actual completed-pullback/integral-direct-image adjunction | `Comparison.integral_transpose` says that the completed Hom bijection is precomposition with the published `pbcActualCompletedPullUnit` followed by `pbcActualDerivedAdjunction`. |
| Actual raw adjunction and its units/counits | `rawAdjunction` is on the dependency's `Along.raw` and the actual `rawPush`. `localized_unit` and `localized_counit` identify its maps with raw localization of the specified integral adjunction's maps. `HEq` handles different functor-expression endpoint presentations; it equates the actual morphisms. |
| Realization respects units and counits under the given pullback comparison | `Comparison.unit` and `Comparison.counit` are explicit equations with `a.comparison.inv` and the ordinary ambient adjunction unit/counit. Both have been checked for source, target and direction. |
| Finite coefficient extensions | `FieldChange.raw_normalization` fixes the raw comparison on integral representatives by exactly `pbcScalarDirectImageIso`. `ambient_mate` fixes the continuous coefficient comparison by the mate of `r.mixed ... .ambient`. `compatibility` equates the two complete routes through the actual realization coefficient comparisons. |
| Successive extensions and the prescribed associators | `FieldComposition.raw` uses `pbcRationalScalarCompComponent`; `FieldComposition.ambient` uses `pbcReductionNormalization` and the exact coefficient-composition equations of `r.fieldComposition`. No new associator is selected. |
| Identity morphisms | `Identity.raw_mate` and `ambient_mate` use the right adjunction transposes of the dependency's actual identity pullback isomorphisms. `compatibility` equates this with the comparison for the identity scheme map. |

Dependency declarations read and used:

- `def-weil-scheme-morphism-properties` is a convention node with no declaration; its finite-type and separated meanings are `AlgebraicGeometry.LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` in Mathlib's morphism files.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`, reexporting the fixed degree, absolute value, integers, uniformizer and quotient constructions of `CoefficientExtension`.
- `Sheaf.Paper.AdicCoefficientDatum`: `Scheme.completedReductionTower` and the completed finite-quotient ring construction.
- `Sheaf.Paper.PbcRationalCategory`: `Scheme.PbcRationalDerivedCategory`, `PbcRationalCategory`, `pbcRationalization`, the constant-section scalar structures.
- `Sheaf.Paper.IntegralUniformCoefficient`: `Scheme.pbcBoundedConstructibleComplete`; the existing `PbcBoundedConstructibleComplete` / `PbcIsBoundedConstructibleComplete` general-datum forms are the exact forms already used by the realization dependency. The unlifted Type(u+1) specialization and the lifted Type(u) specialization do not define a second predicate.
- `Sheaf.Paper.ContinuousRationalDerivedRealization`: `ContinuousRational.Base`, `At`, `Along`, `Family`, `modulePull`, `moduleUnit`, `derivedPull`, `integralPull`, and all the given realization/mixed/coefficient/identity comparisons; the primary recorded theorem is `continuous_rational_derived_realization`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, instantiated by the dependency's `Scheme.pbcModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`, with the existing coefficient categories' canonical derived-category instances.
- `Sheaf.Paper.CompletedDirectImageLimits`: `Scheme.AdicCoefficientDatum.directImageRlimIso`, its strict tower evaluation/projection/completion normalizations.
- `Sheaf.Paper.SfDerivedDirectImage`: `WeilConjectures.SfIntegralDirectImage`, `sfCompletedDerivedDirectImage`, and the finite-reduction comparisons.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`: `Scheme.integralStratifiedPerfectCharacterization`, with the full three-clause integral category and its detailed-coefficient comparison.
- `Sheaf.Paper.SfIntegralDirectImageConstructible`: `WeilConjectures.sfIntegralDirectImage_constructible`, including uniform finite-level bounds and the separate empty case.
- `Sheaf.Paper.PbcRationalTransport`: `CategoryTheory.ScalarLocalization.transport_exact` and the existing `transport` implementation used by `pbcConditionalRational`.
- `Sheaf.Paper.PbcScalarExtension`: `Scheme.pbcCoherentScalarExtension`, `pbcConditionalIntegral`, `pbcConditionalRational`, `pbcScalarDirectImageIso`, `pbcRationalScalarExtension`, `pbcRationalScalarCompComponent`.

The node's recorded proof-dependency modules are also imported privately where they are
not statement imports. The complete 15-step natural-language node proof is preserved in
the primary theorem docstring, with every step's cited node IDs.

Source inspection: opened Bhatt--Scholze PDF via pdftotext, reading Lemma 6.7.2,
Proposition 6.8.14(2), Remark 6.8.15, and the finite continuous coefficient localization
in Lemma 6.8.2. Read current blueprint unit `sk-p-dl-a1-perverse` and the curve-heart
proof Step 3 for the downstream use of actual units and ambient direct image.

Edge cases checked: empty X or Y (no Nonempty premise and the dependency Base allows
topological dimension -infinity); K=0; torsion integral K killed by rationalization;
arbitrary shifts and cohomological bounds; identity scheme morphisms; E=F and identity
field embeddings; successive ramified extensions (no common uniformizer is required);
positive characteristic different from l and characteristic zero. Site objects keep
object universe u+1 and morphism universe u; coefficient module values live in u+1.
No universe equality of those two levels is imposed.

Searches:

- msearch LeanFinder: "Continuous rational realization of constructible adic complexes commutes with derived direct image on pro etale sites". Eight hits: BDeRhamPlus, condensed profinite-solid constructions, limits of affine schemes, and the étale forgetful functor. None states this comparison.
- msearch Loogle: "Functor.rightDerived, SheafOfModules.pushforward". Unknown first identifier and zero hits; checked source APIs directly instead.
- msearch Mathlib grep: "rational.*[Dd]irect|[Dd]irect.*[Rr]ealiz". Zero hits.
- msearch LeanSearch: "Localization of continuous adic coefficient sheaves commutes with derived pushforward of constructible complexes". Eight hits for ordinary sheaf pushforward and site adjunction APIs, including `SheafOfModules.pushforward`; none gives localization commutation.
- rg in upstream WeilConjectures and side lean/Sheaf for rational/direct-image/realization. The side `ContinuousRationalDerivedRealization` gives pullback, not this pushforward statement; `PbcScalarExtension` treats finite coefficient extensions, not localization B -> E. No upstream match for the item ID. Used these existing APIs rather than duplicating their notions.

No STATEMENT-DISPUTED flag and no statement correction. The completed coefficients,
étale-origin witnesses and the actual canonical maps are retained.

## Second reading by NQ

Author's self-check under the dispatcher's explicit single-worker/no-subagent brief;
independent review belongs to the maintainer. Reopened the node and source module,
matched all clauses as above, and checked the mate directions. In particular the unit
uses `a.comparison.inv` after the ambient unit, while the counit uses it before the
realized raw counit. The finite-extension square begins with scalar extension of the
already pushed raw object and ends with ambient F-direct image after the X coefficient
comparison. The associator equations use the existing raw and ambient balancing
comparisons. No second agent or independent approval is claimed here.

Validation: scompile.py compiled the final sandbox module and the module at its library path
with no Lean errors or warnings. Reported compile times: 29.3 s and 20.3 s, within the
unchanged 60-second file limit. The node copy changes only `lean`; all Lean lines are
at most 100 characters, all variables/universes are explicit, and every definition
has actual data.
