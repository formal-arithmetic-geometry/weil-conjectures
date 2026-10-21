## Worker report

Delivered module: `Sheaf.Paper.RationalRealizationPullbackComparison`.
Primary declaration: `AlgebraicGeometry.Scheme.rationalRealizationPullbackComparison`.
The second theorem, `rationalRealizationPullbackModel`, states the perfect local-model
clause. Both proofs are `sorry`. All other declarations are records or actual
composites of the published constructions; there is no postponed data definition.
The original node changes only in `lean`. There are no new or repaired dependency nodes.

I read the item, its seven proof steps, all statement-dependency records and the
recorded declarations and docstrings. I read Bhatt--Scholze Proposition 6.6.11,
Lemma 6.5.9(4)-(5), and Remark 6.8.15 in the local PDF with `pdftotext`, including
the explicit ordinary ringed-pullback formula in the remark. In particular the
ordinary pullback in the comparison must remain distinct from completion.

The following matches every hypothesis and clause. The Lean names below are in
`AlgebraicGeometry.Scheme` unless another namespace is given. Lean uses `g : X ⟶ Y`,
so `Y` is the node's X and `X` is the node's X'.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` in the explicitly bound variable context. |
| Finite E/Q_ell, integers A and its uniformizer | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`, with the existing `PbcIntegralRing l E`, `pbcIntegralDatum l E`, and `pbcUniformizer l E`. The recorded choice of uniformizer is reused. |
| Both schemes noetherian and finite dimensional | `{X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]`, and `[Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]`, likewise Y. |
| Ell invertible on both schemes | `[Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]`, likewise Y. This is invertibility in every local ring. |
| Any morphism | `(g : X ⟶ Y)`, with no smoothness, properness, finite type, separatedness, base field or coefficient-isomorphism assumption. |
| Small pro-etale site and completed coefficient ring | `ProEt.topology`, `pbcAdicCompletion T (pbcIntegralDatum l E)`, with their existing projections. The site object and morphism universes remain u+1 and u; the coefficients and modules are in u+1. |
| E_T is the sheaf localization of B_T | The supplied `sT : RationalModuleRealization l E T` has the recorded `integralIso`, `localizationIso`, `inclusion`, and their normalizations. `rationalPullScalar l E sT` is exactly `sT.integralIso.hom ≫ sT.inclusion`. |
| The integral category includes compatible etale witnesses | `PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)` and `PbcIsBoundedConstructibleComplete`; these are reused, including every field of the existing predicate. |
| Raw rationalization Q, without a Karoubi envelope | `PbcRationalCategory`, `pbcRationalization`. `rationalPullFraction` is literally invSelf(varpi)^n times Q of the numerator. |
| Constructible rational sheaves and J(QK), J(f/varpi^n) | The recorded `RationalModuleRealization` is used unchanged; its `constructible`, `objects`, and `fractions` fields retain the stratified locally finite-free condition and the object/fraction formulas. These are input choices of the functors named in the node, whose existence is the dependency theorem, rather than additional mathematical hypotheses. |
| c_g is fixed by finite projections | `completedCoefficientMap g (pbcIntegralDatum l E)` is used verbatim in `coefficient_square` and in the existing `pbcActualModulePull` and `pbcActualDerivedPull`. |
| Ordinary P_g and specified completed P_g with gamma | `pbcActualDerivedPull`, `pbcActualStrictCompletedPull`, and `pbcActualStrictCompletedPullUnit`. I read `PbcActualStrictPullback`: the last is built from the constant-tower unit and the strict quotient augmentation. It is not replaced by an unnormalized cone comparison or a different completion-reflector unit. |
| Ordinary P_g K is in the integral category | `RationalPullIntegral.ordinary_mem`. |
| Gamma is invertible | `RationalPullIntegral.unit_isIso`, on that exact strict unit. `completed_mem` also records membership of the isomorphic completed object, needed to type Q of it. |
| Perfect local models pull back to the same A-model | `rationalRealizationPullbackModel`: for every `h : S ⟶ T` and actual perfect scalar complex P, ordinary pullback of `(integralConstantDerived T d).obj P` is isomorphic to `(integralConstantDerived S d).obj P`. It applies to the strata and their pulled covering charts; no noetherianity condition is imposed on a covering chart. |
| Completeness and compatible etale origins retained | Membership in the unchanged complete predicate in `ordinary_mem` and `completed_mem`; the main proof docstring explains the pulled strata, uniform reduction bounds and compatible origins. |
| Ordinary rational pullback is E_X tensor over g inverse E_Y | `rationalPullDerived` is the existing exact `adicTowerPullback` into the *inverse-image coefficient ring*, followed by `pbcDerivedExtend` along `rationalCoefficient`. It does not use an arbitrary replacement functor or require an isomorphism of coefficient sheaves. |
| Canonical localization identification, preserving its unit | `rational_normalization` fixes the coefficient map on pulled continuous numerators. `coefficient_square` identifies its restriction to B with the projection-defined integral map followed by localization. The recorded unit-preserving `existsUnique_localizationInverseImage` supplies the canonical identification of the inverse-image localization; this square is the corresponding induced map into E_X. |
| Both ordinary sides flatten to E_X tensor over g inverse B_Y | `moduleComparison` compares the two actual composite scalar extensions. `module_unit` fixes it on inverse-image sections and tensor generators: it sends `1 ⊗ pull(1 ⊗ m)` to `1 ⊗ pull(1 ⊗ m)` in the other association. E_X-linearity and balancing determine the general map, namely the two flattenings through the common tensor. There is no bare unconstrained choice of comparison. |
| Derived flattening on K-flat representatives | `derived_normalization` ties `ordinaryComparison` to `NatIso.mapHomologicalComplex moduleComparison` through the actual ordinary computation counits. The helper `rationalPullComplexCounit` is the composite of exact inverse-image factorization and the existing scalar-extension counit. On the flat-term K-flat class these counits compute the derived tensor operations. |
| Completed comparison alpha and inverse specified unit | `alpha : rawPull ⋙ sX.J ≅ sY.J ⋙ rationalPullDerived ...`. `alpha_normalization` says F(gamma) followed by alpha equals `ordinaryComparison`, inserting only the dependency's J(QK)=F(K) object equalities and `raw_objects`. Since gamma is invertible this is precisely alpha = flattening after F(gamma inverse). |
| Descends on every raw fraction | `raw_objects` gives Q of the exact completed integral object; `raw_fractions` gives completed pullback of f over the same varpi^n, with only the necessary object-equality transports. `alpha` is a natural isomorphism of the raw functors, hence its naturality applies to every fraction and every equality of fraction representatives. |
| No assumption g inverse B_Y is B_X | There is no such binder, field or input. The rational coefficient map is a morphism, not an isomorphism. The auxiliary exact inverse image uses only the reflexive identification of its own inverse-image ring; subsequent scalar extension uses the actual map. |

Dependency declarations used, read at the recorded module paths:

- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Topology.FiniteLocallyClosedStratification` and
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`, through the realization data.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and its tensor structures, used by scalar extension.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, through the recorded realization data.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and its imported integer/uniformizer constructions.
- `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower`, its augmentation and the
  coefficient/projection constructions underlying the strict unit.
- `Sheaf.Paper.IntegralUniformCoefficient`: `pbcBoundedConstructibleComplete`, with the
  underlying `PbcIsBoundedConstructibleComplete` reused at the existing lifted integers.
- `Sheaf.Paper.PbcQbarCompletedPullback`: the recorded node's imported integral interface
  `pbcActualStrictCompletedPull` and `pbcActualStrictCompletedPullUnit` in
  `Sheaf.Paper.PbcActualStrictPullback`; its Qbar specialization is not substituted here.
- `Sheaf.Paper.ContinuousConstructibleModule`: `AlgebraicGeometry.ProEtale.IsContinuousConstructible`,
  with the realization dependency's stated rational locally finite-free specialization.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `ProEt` and `ProEt.topology`.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`, `pbcRationalization` and the recorded
  `PbcRationalDerivedCategory` convention.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, namely the
  existing `SheafOfModules` category used by `pbcModules`.
- `Sheaf.Paper.RationalModuleRealizationFunctor`: `RationalModuleRealization`, its
  `objects`, `fractions`, `integralIso`, `inclusion`, and `rationalModuleRealizationFunctor`.
- `Sheaf.Paper.OrdinaryCompletedIntegralPullback`:
  `WeilConjectures.ordinaryCompletedIntegralPullback`. Its separately normalized cone-model
  unit is not identified with the strict pbc unit merely by their projections.
- `Sheaf.Paper.ConstantCompletionEquivalence`: `CategoryTheory.ConstantCompletion.equivalence`
  and its imported coefficient/finite-reduction comparisons, underlying the specified-unit interface.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`: `integralStratifiedPerfectCharacterization`
  and the public `integralConstantModule`, `integralConstantDerived`, `IsIntegralStratifiedPerfect`.
- `Sheaf.CategoryTheory.LocalizationInverseImageCoherence`:
  `CategoryTheory.existsUnique_localizationInverseImage`, its unit and derived comparison.

The public realization dependency already imports the statement modules. The file also
imports the remaining recorded, stated proof-only dependencies explicitly; the finite DVR quotient leaf
is supplied through the coefficient-extension module and its Mathlib imports. Additional
reused constructions are `pbcConditionalIntegral` from `PbcScalarExtension` and the
ordinary inverse-image generators/factorizations from `ProEtaleDerivedPullbackComposition`.

Searches actually run using `batch2/msearch.py`, group Q06 and this item:

- LeanFinder: "Rational realization of completed integral constructible pullback via inverse
  specified quotient tower completion unit". Eight hits on ordinary adic completions,
  `galLift` and Laurent series; none states this comparison.
- Loogle: `SheafOfModules.pullback`. Twelve hits give ordinary pullback, composition and
  its adjunction. No completed-constructible/rational comparison or specified strict unit.
- Mathlib grep: `[Cc]ompleted.*[Pp]ullback|[Pp]ullback.*[Cc]omplet`. Eight unrelated topology,
  manifold and order hits; no matching declaration.
- LeanSearch: "Derived module pullback commutes with rationalization of complete constructible
  adic complexes". Eight hits on ordinary sheaf/module pullback and its composition; no match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for rational/pullback and realization/pullback,
  and `grep -rn` for the exact node id in `WeilConjectures`: no exact match.
  `Sheaf.Paper.RealizationCompletedPull` was read in full. Its theorem requires finite-type
  separated schemes over a field, so it does not state this arbitrary-morphism node.
- Exact-name search of the project and `dag/lean_names_upstream.json` found no preexisting
  declaration of the new comparison name. These helper abbreviations merely name composites
  needed for this node; they do not redefine the library's modules, localization or tensor.

Edge cases checked against the formulas: empty schemes and empty strata (no nonemptiness
binder); K=0 and the zero perfect model; the identity morphism; n=0 in fraction morphisms
(denominator one); torsion models, whose rational realization is zero; arbitrary unbounded
ambient complexes for the ordinary derived comparison; a nonflat finitely presented scalar
module (no flatness assumption on such a module); and a pro-etale chart that is not
noetherian. The global scheme finiteness assumptions never restrict the local-model theorem.
The site object and morphism universes are not equated.

No statement correction or STATEMENT-DISPUTED issue was needed.
Compilation with the required `scompile.py` succeeded with no errors or warnings.
The first revision using an additional rational coefficient isomorphism was removed during
second reading; the final interface uses the actual morphism and derived scalar extension.

## Second reading by Q06

The dispatcher brief prohibits starting other agents and assigns the independent review
to the maintainer. Accordingly this section records a separate second pass by this worker,
not a claimed independent agent review. I reopened the original node and the final module
and checked the hypothesis/clause table above against both.

The first pass had used the existing isomorphism-valued `proEtaleRingDerivedPullback` API
for the whole rational pullback. This would add an unnecessary coefficient-isomorphism
conclusion. I replaced it with exact inverse image into its own inverse-image ring followed
by `pbcDerivedExtend` of the canonical map. The ordinary tensor-generator formula and the
cochain computation-counit equation were changed to use that exact composite. Compilation
then exposed opacity of the module composite during zero-morphism instance synthesis;
making that composition an `abbrev` reuses its factors' existing additive instances without
adding a new assertion.

I checked the source and target of `alpha_normalization` separately: it starts at F_X(P_g K),
passes through F_X(gamma), the recorded J_X object formula and raw-object transport, alpha,
and the J_Y object formula on the right. It ends at rational ordinary pullback of F_Y(K).
Thus cancellation gives precisely F_X(gamma inverse) followed by the canonical ordinary
comparison, with the direction required by the node. The two object transports in the
fraction formula point from rawPull(QK) to Q of the completed object and back at L.
Membership uses the original three-part predicate, so compatible etale origins were not
silently discarded. The local-model theorem retains a genuinely perfect scalar complex,
not an unconstrained comparison object. No remaining mismatch was found.

Validation: the prescribed `deliver2.py --no-push` returned `OK (dry run)`: the
packet passed server preflight and compilation; nothing was pushed by that check.
