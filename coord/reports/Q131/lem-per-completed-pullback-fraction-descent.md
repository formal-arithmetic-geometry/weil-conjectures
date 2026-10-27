## Worker report

The module `Sheaf.Paper.CompletedPullbackFractionDescent` states
`AlgebraicGeometry.Scheme.CompletedPullbackFractions.completedPullbackFractionDescent`.
Its conclusion `Nonempty (Descent ...)` packages every clause of the assigned node.
There is one postponed theorem, with exactly `by sorry`, and its docstring gives the
node's six-step proof. No definition selects data from this existence theorem.
`Descent` is the output record itself; the other helpers transparently expose existing
objects, maps, fractions and the realization witness's scalar action.

Hypotheses and objects, read against the node:

- The prime is `(l : ℕ) [Fact l.Prime]`; the finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  `PbcIntegralRing l E` is the dependency's size lift of the actual valuation subring,
  and `pbcUniformizer l E` is its recorded uniformizer. This changes size only.
- The node's `g : X' → X` is spelled `g : X ⟶ Y` here (X is the source).
  Both schemes have `IsNoetherian`, `Fact (∃ n, topologicalKrullDim ... ≤ n)`, and
  `Fact (∀ x, IsUnit (l : ...presheaf.stalk x))`. The last condition is precisely
  invertibility of l on the scheme, including the empty scheme. There is no base
  field, nonemptiness, smoothness, or isomorphism hypothesis on g.
- The small pro-etale sites are `Scheme.ProEt` with `ProEt.topology`.
  `pbcAdicCompletion W (pbcIntegralDatum l E)` is the already constructed limit
  of quotient coefficient sheaves; natural level n represents exponent n+1.
  Coefficients and site objects live in u+1; site morphisms remain in u.
- Ordinary unbounded categories are `DerivedCategory (pbcModules W ...)`.
  `Integral` abbreviates the existing `PbcBoundedConstructibleComplete`, whose
  predicate includes completeness, uniform constructible reductions, and compatible
  etale origins. `Rational` and `Q` abbreviate the recorded raw scalar localization
  and its integral functor. There is no new category or completion.
- `completedCoefficientMap g (pbcIntegralDatum l E)` is the projection-defined c_g.
  `completedOrdinaryPullback` is the ordinary derived inverse image followed by
  scalar extension along exactly that map. `pbcActualStrictCompletedPull` retains
  the published strict reduction-tower/derived-limit completed pullback.
- `hP` says that the ordinary pullback preserves the specified full subcategory.
  `hγ` says that the **specified** `completedPullbackComparison` is invertible at
  every integral object; no arbitrary natural isomorphism replaces it.
- `JY` and `JX : RationalModuleRealization ...` are arbitrary supplied normalized
  realizations from the recorded dependency. Its `integralIso`, `localizationIso`,
  `inclusion`, `objects` and `fractions` give precisely the specified model of
  `B_W[1/varpi]` and `J_W`. No full-faithfulness property is part of this structure.

Conclusions, clause by clause (fields of `Descent`):

- `coefficient_constants` is equality of maps from the inverse image of the entire
  constant valuation-ring sheaf. It states preservation of **every** A-scalar,
  through `proEtaleConstantInverseImageMap` and `pbcCompletedScalar`.
- `ordinary_additive` and `ordinary_linear` say the actual ordinary restriction is
  A-linear. `completed_mem`, `completed_additive`, and `completed_linear` give the
  completed restriction and its A-linearity. Both restrictions use the existing
  `pbcConditionalIntegral`; its underlying object and arrow maps are unchanged.
- `conjugation` states literally `hatP(f) = gamma_K^(-1) ≫ P(f) ≫ gamma_L`, with
  Lean's left-to-right composition order. The inverse takes exactly `hγ K`.
- `bar` is the raw rationalized functor; `bar_objects` is the exact object formula
  `bar(Q K) = Q(hatP K)`; `bar_fractions` is the required formula on every fraction.
  The `eqToHom` terms only transport along `bar_objects`. `bar_additive` records
  preservation of sums; preservation of identities and composition is in its
  `Functor` structure.
- `fraction` is `invSelf(varpi)^n • Q.map f` in the existing tensor Hom module.
  `fraction_eq` gives the iff with existence of r annihilating the cross-multiplied
  difference; `annihilator` asserts preservation of that **same r**. There is no
  cancellation, injectivity assumption, or torsion-free hypothesis.
- `fraction_add` states `(varpi^m f + varpi^n h)/varpi^(n+m)` and `fraction_comp`
  states `(f ≫ h)/varpi^(m+n)`, exactly the source's fraction operations.
- The extension of H is literally `bar ⋙ JX.J`. The extension of G is literally
  `JY.J ⋙ rationalPull l E g`. `rationalPull` is ordinary derived pullback for the
  normalized continuous-precomposition map of the rational coefficient sheaves.
  In the supplied realization model this is exactly localization of c_g, not an
  arbitrary map. `H_fractions` and `G_fractions` state the scalar formula for either
  extension. `realizationSmul` only activates `JX.moduleLinear` and uses the existing
  induced derived action; it defines no new scalar structure.
- `comparisons` quantifies over every beta from the **specified integral H**
  `(hatP ⋙ Q_X) ⋙ J_X` to the integral restriction of G. It asserts a unique
  natural transformation between the two rational extensions. Its components are
  beta's components, transported only by `JX.J.map (eqToHom (bar_objects K))`.
  In particular this is not restricted to invertible beta. Substitution of the two
  fraction formulas in its naturality equation gives precisely the displayed
  varpi^(-n)-multiple of integral naturality in the node (Lean composes left to right).
- `comparisons_iso` says that any such extension is an isomorphism when every
  integral beta component is invertible. All equations live in the target category;
  no argument requires J to be faithful.

Dependency declarations used (modules read with their recorded signatures/docstrings):

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, via the existing tensor/derived constructions.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; and `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the existing
  `Padic.finite_coefficientExtensionRing` and its publicly retained valuation ring,
  uniformizer, ideal and quotient constructions.
- `Mathlib.CategoryTheory.Linear.Basic`: `CategoryTheory.Linear`;
  `Mathlib.CategoryTheory.Linear.LinearFunctor`: `Functor.Linear` and Additive.
- `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower` and its actual
  completed-ring/projection/quotient constructions, publicly retained by the pullback.
- `Sheaf.Paper.IntegralUniformCoefficient`: `pbcBoundedConstructibleComplete`,
  publicly retaining `PbcBoundedConstructibleComplete` and the coefficient encodings.
- `Sheaf.Paper.PbcQbarCompletedPullback`: recorded dependency module, publicly
  retaining `completedCoefficientMap`, `completedOrdinaryPullback`,
  `completedPullbackComparison`, `pbcActualStrictCompletedPull` and its unit.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`, `pbcRationalization`,
  `pbcCompletedScalar`, and the inherited integral A-linear structures.
- `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`:
  `ringedLocalizationRingOfUniverses`; this is the sheaf localization used in the
  realization witness's specified localization comparison.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, retaining exactly
  Mathlib's `SheafOfModules` used by `pbcModules`.
- `Sheaf.Paper.RationalModuleRealizationFunctor`: `RationalModuleRealization` and
  `rationalModuleRealizationFunctor`; all coefficient/model normalizations are reused.
- Added the already landed statement dependency
  `lem-weil-pbc-continuous-coefficient-general-pullback-isIso`, module
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientGeneralPullbackIso`:
  `rationalContinuousPullback`, `rationalContinuousPullback_normalized`,
  `rationalContinuousPullback_isIso`. This supplies the canonical rational coefficient
  map in the realization model. No node text or dependency record is repaired.

All stated proof-dependency modules are imported, including the independent-universe
ringed-topos derived pullback, K-flat resolutions, coefficient actions, inverse image,
integers localization, localization/inverse-image coherence, module localization and
localization/base-change comparison. The theorem docstring identifies their use in
all six proof steps.

Edge cases checked before writing:

- Empty source or target schemes are retained: stalk invertibility is vacuous there
  and no nonempty base-field or characteristic condition is added.
- Zero objects and zero/torsion Hom modules are retained. A nonzero integral map
  killed by varpi becomes zero; the existential r in `fraction_eq` handles this.
- Denominator exponents n=0, m=0, and annihilating exponent r=0 are included.
  Numerator zero and arbitrary sums/composable arrows are included.
- g may be the identity or an arbitrary scheme morphism. The statement never
  assumes inverse image preserves the infinite limit, or that c_g is invertible.
- beta need not be invertible. Uniqueness uses unchanged raw objects, not faithfulness.
- The source/target site object and morphism universes have not been equated.

Searches (the prescribed wrapper logged their exact outputs in searches.jsonl):

- LeanFinder: “Derived pullback preserves constant scalars and descends to localization
  fractions with natural transformations”: 8 hits, including exact-derived functor
  linearity and abstract localization linearity; none states this geometric descent.
- Loogle: `CategoryTheory.Functor.Linear`: 12 hits, including `linear_of_iso`,
  full-subcategory linearity and functor composition; reusable ingredients only.
- LeanSearch: “A linear functor extends to fractions and every natural transformation
  descends uniquely to scalar localization”: 8 hits, including `natTransExtension`
  for abstract localization and linear module scalar extension; no complete match.
- Mathlib grep via msearch: `linear_of_iso|natTransExtension` in CategoryTheory:
  8 hits in LinearFunctor and Localization/Construction/Linear, not the assigned statement.
- Project rg searches for `completedPullback`, `fractionDescent`,
  `rationalModuleRealization`, `rawFraction`, `linear_of_iso`, and the exact item id
  in `lean/WeilConjectures` and `lean/Sheaf` found the reusable constructions above,
  automorphism-only linearity, and descent systems with stronger prescribed input
  data. None states the assigned result for arbitrary g and arbitrary integral beta.
  The aliases in this module are not second constructions of any existing notion.

The source was checked directly with pdftotext: Remark 6.8.15 gives ordinary pullback
as naive inverse image followed by coefficient tensor; Section 6.8 rationalization
supplies the localization context. The detailed scalar/fraction calculations are
explicitly marked agent elaboration in the assigned node. No statement fault or
STATEMENT-DISPUTED flag was found. The node's statement and proof remain unchanged.

## Second reading by Q131

I reread the actual node and module after compilation; this is a separate second pass
by this worker, since the dispatcher expressly prohibits starting other agents.
I matched every hypothesis and clause as listed above, and checked the six proof
steps against the source. The first compile exposed the missing activation of the
realization witness's scalar action; the real-data `realizationSmul` helper fixes it.
The second pass also replaced a comparison formulated on the literal restriction of
H's extension by one on the specified integral H itself, with its required canonical
object-equality transport. Conjugation now states the actual inverse-gamma formula.
No integral linearity or rational faithfulness is assumed in place of a conclusion.
The existing continuous-precomposition coefficient map is cited through its landed
node. No new nodes, dependency modules, or statement correction are required.
