## Worker report

The main module states `AlgebraicGeometry.Etale.unbounded_abelian_exchange_comparison`.
Its only theorem has proof `by sorry`. The two comparison definitions have real data:
termwise descent of the existing inverse-image coefficient isomorphism, and its
canonical derived adjunction mate. There are no chosen arbitrary transformations,
no Nonempty choices of maps, and no new definition nodes.

Hypotheses and clauses, in the order of the node:

- An arbitrary commutative ring is `(Λ : Type (u + 1)) [CommRing Λ]`, the established
  coefficient universe for `Scheme.{u}`. No nonzero, finite, torsion or flatness assumption.
- The four schemes and four morphisms are explicit binders; the Cartesian square with
  chosen identification is `sq : ChosenCartesianSquare g' f' f g`.
- `DerivedCategoryModule Λ X` is the existing unbounded module derived category.
  The abelian category is `DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat)`.
  No boundedness restriction is present.
- The forgetting functor is exactly `D(moduleAbelianForget Λ T)`, the termwise-derived
  existing `sheafCompose` with `forget₂ (ModuleCat Λ) AddCommGrpCat`.
- The first conjunct gives finite-limit and finite-colimit preservation for the sheaf
  functor, `IsTriangulated` for its unbounded derived functor, and
  `ReflectsIsomorphisms` for the latter. The homology-functor natural isomorphism
  states `H^i(UK) ≅ U(H^i K)` for every integer, with the standard natural categorical
  identification in place of literal equality between independently constructed objects.
  Quantifying over all schemes expresses the uniform corner-wise assertion.
- For every scheme morphism v, `moduleAbelianUnboundedUpperStarIso Λ v` is a natural
  isomorphism in the direction `U_A v^-1_Λ ≅ v^-1_Ab U_B`. Its construction is the
  inverse of the existing unit-compatible underived comparison, descended via
  `mapDerivedCategoryNatIso` and the localization composition isomorphisms.
- `moduleAbelianUnboundedLowerStarComparison Λ v` is an actual natural transformation
  `Rv_*Λ ⋙ U_B ⟶ U_A ⋙ Rv_*Ab`, fixed as the derived mate, not an existential map.
  The second conjunct asserts its invertibility and its normalization on every
  homotopy complex by `rightDerivedFunctorUnit` and the exact-forgetting factorization
  `mapDerivedCategoryFactorsh`. Direct image commutes definitionally with forgetting,
  so no missing underived identification is suppressed in this equation.
- This derived-unit normalization is an equivalent precise characterization of the
  resolution construction prescribed in the node. For a module K-injective I and any
  abelian K-injective replacement j:UI→J, naturality of the abelian derived unit gives
  `γ_Ab(UI); Rv_*Ab(Qj) = Q(v_*j); γ_Ab(J)`. The displayed normalization substitutes
  the left side for `U(γ_Λ(I)); b(QI)`, through the explicitly displayed forgetting
  factors. Since γ_Λ(I), γ_Ab(J) and Qj are invertible, it identifies b with exactly
  the class of `v_*UI→v_*J`. It does not assert UI is K-injective.
- The final equation expands both endpoint composites rather than naming copies of
  them: after `U(Ex_Λ)` are `b_f'(g'^* K)` and `Rf'_*Ab(a_g'(K))`, hence precisely t_K.
  Before `Ex_Ab(UK)` are `a_g(Rf_*Λ K)` and `g^*Ab(b_f(K))`, hence precisely s_K.
  These are isomorphisms because a is an isomorphism by construction and the second
  conjunct makes b invertible. Lean's `≫` writes categorical composition in traversal
  order, so the equation is exactly `t ∘ U(Ex_Λ) = Ex_Ab ∘ s`.
- Both exchanges are the canonical exact-inverse-image adjunction mates supplied by
  the repaired `def-kun-unbounded-exchange`, with no assumed or concluded exchange
  invertibility. Properness, torsion and finiteness are absent throughout.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `AlgebraicGeometry.ChosenCartesianSquare`
  and its inherited `toCommSq`, retaining the specified Cartesian identification.
- `Sheaf.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`; `DerivedCategory.homologyFunctor`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the small-etale sheaf encodings
  and global derived-category conventions; its current source was read through
  `scompile.py --source` because absent from the older source checkout.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`:
  `CochainComplex.IsKInjectiveResolution`, `CochainComplex.IsKInjective`, `QuasiIso`.
  Resolution normalization uses the same K-injective model through the generic
  `rightDerivedFunctorUnit`, and never assumes forgetting preserves K-injectives.
- Added the already recorded dependency
  `lem-weil-pbc-module-abelian-derived-direct-image-comparison`, module
  `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`:
  `moduleAbelianForget`, its exactness/additivity instances,
  `moduleAbelianUpperStarIso`. Its bounded-below comparison theorem is not substituted
  for the unbounded assertion. No dependency node is duplicated.
- The repaired dependency module `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`:
  `exactDerivedSquareUpperStarIso` and `exactDerivedBaseChangeMap`.
- Generic upstream/Mathlib constructions: `Functor.mapDerivedCategory`,
  `Functor.mapDerivedCategoryNatIso`, `Functor.mapDerivedCategoryCompIso`,
  `Functor.mapDerivedCategoryFactorsh`, `Etale.squareUpperStarIso`,
  `Etale.mapDerivedUpperStarLowerStarAdjunction`, `Functor.rightDerivedFunctorUnit`,
  and `CategoryTheory.mateEquiv`. Their types and characterization docstrings were read.
- Stated proof dependencies are imported without `public`: `RingedSiteModules`,
  `EtaleInverseImageModulesExact`, `RingedToposDerivedPushforwardComposition`,
  `ExactFunctorDerivedFunctor`, and `DerivedCategory.AdjointSquareComparison`.
  Other proof dependencies have Mathlib matches and no separate project module.

Sources read: Stacks `sites-cohomology.tex`, remark-base-change (07A7) and
lemma-modules-abelian-unbounded (0D6J), especially the explicit choice I→J and the
class of the direct-image map; the node's full five-step proof, and the generic
unbounded exchange and exact-functor source interfaces.

Edge cases checked: the zero ring is permitted; zero complexes and the empty scheme
are permitted; identity edges and identity squares use the same mate definitions;
there are no truncations or degree-sign restrictions. The ring and abelian sheaf
carriers use the existing common u+1 convention, and no equality of site object and
morphism universes was imposed. All universe and variable binders are explicit.
No statement dispute or source correction is needed.

Searches performed:

- `msearch.py leansearch`: “Forgetting module coefficients commutes with unbounded
  derived etale direct image and canonical base change”: service unavailable
  (Internal Server Error); no mathematical verdict inferred from that failure.

- `msearch.py leanfinder`: “Forgetting module coefficients commutes with unbounded
  derived etale inverse image and direct image and base change exchange”: eight
  results, all etale algebra/Kaehler differential results, no matching theorem.
- `msearch.py loogle`: `sheafCompose, mapDerivedCategory`: no hits; service reports
  unknown identifier sheafCompose.
- `msearch.py grep`: `sheafCompose.*(upperStar|lowerStar)|[Ff]orget.*[Dd]erived`:
  zero Mathlib hits.
- `rg` over upstream WeilConjectures and `lean/Sheaf` for
  `forget.*(derived|baseChange)|(derived|baseChange).*forget` and the item id:
  found the existing bounded-below ModuleAbelian comparison family, read in full;
  no existing unbounded abelian exchange theorem.
- DAG search for forget/coefficient/module-abelian nodes found and checked the
  module inverse-image comparison, bounded-below exchange, and unbounded restriction
  of scalars isomorphism criterion. The latter only compares invertibility and does
  not state this canonical abelian exchange equality or its resolution normalization.
- `rg` for all new declaration names in Mathlib/upstream/project name locations:
  no existing exact generic interface or unbounded module-abelian helpers.

Validation: both modules compiled separately in dependency order using scompile.py,
with no errors or warnings. The first draft exposed the unavailable monoidal abelian
interface, repaired below; the final code adds no monoidal requirement.

## Dependency modules

`def-kun-unbounded-exchange`: its recorded `Etale.derivedBaseChangeMap` uses L(u^*)
and requires monoidal, symmetric closed, and functorial flat-resolution structures
on the coefficient category. ModuleCat supplies these, but AddCommGrpCat does not
have the required monoidal instances in this library. The original record therefore
cannot express the node's abelian specialization. `ExactUnboundedExchange.lean`
repairs the interface under §1(B), with unchanged natural-language statement and
all other node fields. It descends `squareUpperStarIso` termwise by the existing
localization composition and natural-isomorphism operations, then takes its mate
under `mapDerivedUpperStarLowerStarAdjunction` for f and f'. This is exactly the
node's definition with exact inverse image, for both ModuleCat and AddCommGrpCat.
The former L construction is canonically this one under the upstream
`leftDerivedUpperStarIsoMapDerivedCategory`; its composition comparison was already
transported from this termwise comparison. The repair constructs no arbitrary map,
uses no choice or postponed data, and asserts no theorem. All helper declarations
are listed in the owning nodes' lean.declarations and have source/blueprint docstrings.

## Second reading by NF

I independently read the item's full node and both delivered Lean modules, the
recorded dependency signatures, Stacks sites-cohomology.tex at 0D6J(3) and 07A7,
and the blueprint source of def-kun-unbounded-exchange. There is no
statement_change and no new definition node in this packet.

Objects, hypotheses and conclusions, matched in node order:

1. Any commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ]`.
   Verdict: exact match under the recorded derived-category size convention;
   no nontriviality, torsion, flatness or finite-generation hypothesis.
2. Four schemes and the four named arrows: the explicit Scheme.{u} binders and
   f, f', g', g. Cartesian square: `sq : ChosenCartesianSquare g' f' f g`.
   I read its structure: isoPullback and both projection equations give precisely
   the dependency's chosen Cartesian identification. Verdict: match.
3. Ordinary unbounded categories: `DerivedCategoryModule Λ X` unfolds to the
   ModuleCat-valued small-etale sheaf derived category; the abelian category uses
   `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`. I read DerivedCategories
   and the current EtaleSheaves source via scompile --source. Verdict: match;
   no Plus or Bounded restriction is substituted.
4. Termwise forgetting U: `D(moduleAbelianForget Λ T)`. I opened its owning
   module: the abbreviation is sheafCompose of forget₂ ModuleCat AddCommGrpCat,
   not a new module-sheaf construction. Verdict: match.
5. Exactness and conservativity: finite-limit/finite-colimit preservation of
   the additive sheaf functor, IsTriangulated of D(U), and ReflectsIsomorphisms
   of D(U). The homology-functor natural isomorphism for every `i : ℤ` gives
   the stated cohomology identification, with the correct U on sheaf cohomology.
   Verdict: match. The quantifier over T expresses the uniform assertion for
   arbitrary corners; it supplies no hypothesis on the square.
6. Canonical a_u: moduleAbelianUnboundedUpperStarIso has source
   D(u^*_Λ) ⋙ D(U_A) and target D(U_B) ⋙ D(u^*_Ab), hence the node's direction
   U_A u^*_Λ → u^*_Ab U_B. Its data is the inverse of the existing underived,
   unit-compatible moduleAbelianUpperStarIso, descended by mapDerivedCategoryNatIso
   and the two composition isomorphisms. Verdict: canonical termwise match.
7. Canonical b_u: moduleAbelianUnboundedLowerStarComparison has source
   R(u_*Λ) ⋙ D(U_B) and target D(U_A) ⋙ R(u_*Ab). Its data is the mate of a_u^{-1}
   under the two canonical derived adjunctions; the theorem asserts IsIso for
   every v. Verdict: direction and naturality match.
8. Resolution prescription for b_u: the equation for every homotopy complex P
   is the right-derived-unit factorization, with both mapDerivedCategoryFactorsh
   identifications shown explicitly. I checked rightDerivedFunctorUnit in its
   source: its component on a K-injective is invertible. Apply the equation at
   a module K-injective I, then compose with R(u_*Ab)(Qj) for any abelian
   K-injective replacement j:UI→J. Naturality of the abelian unit changes the
   result to Q(u_*j) followed by the invertible unit at J. Thus the equation
   identifies this fixed mate with precisely the class prescribed in 0D6J.
   Conversely that resolution construction has the displayed factorization.
   Verdict: equivalent normalization, no preservation of K-injectivity by U.
9. Endpoints: the left side after U(Ex_Λ) is b_f'(g'^*K) followed by
   Rf'_*Ab(a_g'(K)), exactly t_K. The right side before Ex_Ab is
   a_g(Rf_*Λ K) followed by g^*_Ab(b_f(K)), exactly s_K. All four components
   are isomorphisms by the definitions and the preceding conjunct. Verdict:
   exact typed composites, in traversal order for Lean's `≫`.
10. Exchange equality: the final `∀ K` equates those two composites with
    exactDerivedBaseChangeMap at ModuleCat and AddCommGrpCat. Verdict: exactly
    t_K U(Ex_Λ)=Ex_Ab s_K; neither exchange is asserted invertible. Properness,
    torsion, coefficient finiteness and boundedness do not occur as hypotheses.

Dependency-module reading (H13): def-kun-unbounded-exchange's old recorded
DerivedUnbounded interface requires MonoidalCategory, MonoidalPreadditive,
SymmetricCategory, MonoidalClosed and functorial flat resolutions. I opened that
source and UpperLowerStar. The latter's mapDerivedUpperStarLowerStarAdjunction
uses exact inverse image and needs none of those tensor hypotheses. The delivered
ExactUnboundedExchange descends the existing squareUpperStarIso termwise and
uses mateEquiv with those adjunctions. I checked mateEquiv's input and output
directions against the node's counit composite and 07A7. This repairs the
unusable abelian specialization without altering the notion: on module
coefficients it is the old L construction transported to exact D inverse image.
Both helpers have real data and are listed in lean.declarations; the dependency
node changes only lean, with the required explanation. No private definition,
arbitrary comparison, proof-only choice or duplicate independent notion appears.

Edge cases: zero ring, zero complex, empty schemes, identity arrows and identity
squares remain allowed. All integer degrees, including zero and negative degrees,
are quantified. There is no index-family or characteristic restriction. Universes
and all variables are explicitly bound; the common coefficient u+1 convention
is inherited from the existing categories, not an equality of site universes.

Independent searches used different wording from the worker:

- msearch leanfinder: “Restriction of scalars to abelian sheaves commutes with
  total derived pushforward and Beck Chevalley maps”: eight underived sheaf and
  presheaf pushforward hits. I opened Mathlib's pushforwardNatIso at
  Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:228; it changes a
  continuous functor along an isomorphism, and is not this derived comparison.
- msearch loogle: `"forget", "rightDerivedFunctorUnit"`: zero hits.
- msearch grep: `forget.*rightDerived|rightDerived.*forget`: zero hits.
- rg over Mathlib, upstream WeilConjectures and project lean/Sheaf for
  `abelian.*exchange|exchange.*abelian|forget.*[Kk][Ii]njective|[Kk][Ii]njective.*forget`:
  inspected ModuleAbelianDerivedExchangeCompatibility and the underlying
  ModuleAbelianDerivedDirectImageComparison. Their statements use R+ and D+
  and a Plus object, so neither is the unbounded assertion. The stalk exchange
  results concern stalk groups rather than natural transformations on D.

No mathematical mismatch was found and no Lean or node text was rewritten.
The source/proof docstring contains all five steps of the node's argument; the
only postponed theorem is the owning node's theorem with `by sorry`. The two
helper definitions contain no sorry. The second reading adds this report only.

Second-reader validation: scompile.py compiled both delivered files separately
in dependency order, including library confirmation, with no errors or warnings
(ExactUnboundedExchange 2.4 s; UnboundedAbelianExchangeComparison 8.8 s).
Both node lean.statement strings were checked verbatim against their modules.
