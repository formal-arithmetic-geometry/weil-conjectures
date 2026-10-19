## Worker report

The module `Sheaf.Paper.FiniteTateSiteDescent` states
`AlgebraicGeometry.Scheme.finite_tate_site_descent`. Its only theorem has proof `sorry`.
The twelve supporting definitions/abbreviations have concrete data and are recorded in
`lean.declarations`. They are notation, coefficient encoding transport, local tensor
constructors, or normalization predicates belonging to this comparison, rather than
independent replacement definitions of the Tate objects. No node statement was corrected,
no dependency record was repaired, and no new DAG node was needed.

Hypothesis and conclusion correspondence:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite extension F/Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The quotient uses the recorded valuation ring and chosen
  uniformizer of `Padic.coefficientExtensionRing`.
- Positive coefficient exponent: the Lean parameter `n : ℕ` represents the paper's
  `n+1`, following the recorded finite pro-etale twist. Every positive exponent occurs,
  including 1. `finiteTateCoefficient l E n` is exactly
  `ULift (Padic.coefficientExtensionRing l E (n+1))`.
- Scheme on which ell is invertible: `T : Scheme.{u}` and
  `hT : IsUnit (l : Γ(T, ⊤))`. Invertibility of this constant global section is equivalent
  to invertibility on T. The analogous proof on T' in the pullback clause follows by
  pulling the unit along v, so it places no restriction on the scheme morphism.
- Positive annihilating exponent: `r : ℕ` represents the paper's `r+1` and
  `hA : ((l ^ (r+1) : ℕ) : finiteTateCoefficient l E n) = 0`. The explicit inner
  natural-number cast ensures this is the annihilation hypothesis expected by the
  finite etale Tate construction. No exact order, flatness or ramification assumption
  is imposed.
- The etale first twist is the existing `finiteEtaleTateTwist T (l^(r+1)) _ hA 1`,
  definitionally `finiteEtaleTateLine`, the sheafification of
  `A tensor_(ZMod m) mu_m`. Symmetry identifies this order with the displayed order in
  the node. No etale root sheaf or tensor is redefined.
- The pro-etale target is the existing `finiteCoefficientTwist l E T n (k : ℤ)`.
  `finiteTateProSheaf` only expresses it in fixed-ring module-valued sheaves, using
  restriction along `constantCommuteCompose` followed by the existing
  `constantRingModuleRestriction`. This retains its underlying abelian sections and
  restricts its action to constant scalars; it does not replace its integral tensor
  reduction by a root sheaf of a conveniently chosen exponent.
- The requested canonical isomorphisms are the existential family `b`, at `k=1` and
  every `k : ℕ`. They use the recorded `ProEtale.comparisonUpperStar`, namely the
  module-valued inverse image of `proEtaleSiteComparisonModules`.
- Canonicity is the first conjunct `IsFiniteTateSiteComparison`. For every etale U,
  every pro-etale W over U, scalar a, tuple of finite etale roots z and compatible
  tuple x in the actual root limit, it equates the image of the restricted adjunction
  unit on the etale tensor with the prescribed integral-then-finite pro-etale tensor.
  Compatibility is tested by equality of the actual units under the actual root
  projections. The arbitrary W is essential: no lift to the infinite tower over U
  itself is assumed. This specifies the normalized comparison, not an arbitrary iso.
- Tensor powers: `k : ℕ` is unrestricted. The two power-generator definitions recurse
  with the recorded tensor products and their canonical maps from sectionwise tensors.
  At zero they are constant coefficient sections, at one the recorded root tensors,
  and at k+2 the previous generator tensor the next root generator. Thus the same
  normalization in every k identifies the tensor powers of the first comparison,
  with the coefficient-ring identity at zero. It cannot independently rescale powers.
  The dependency `Etale.derivedTensor` is the existing unbounded K-flat total tensor
  convention. The node states the sheaf-level power comparisons with that convention;
  it does not ask for a new definition of derived tensor. Step 7 of the proof docstring
  describes their termwise/derived interpretation with this exact convention.
- Scheme pullback: the second conjunct quantifies over every v:T'→T and gives c,d,
  each normalized on the same root tensors (`IsFiniteTateEtalePullback` and
  `IsFiniteTateProPullback`). The latter tests every projection of the infinite tower,
  without assuming that inverse image commutes with the inverse limit. The displayed
  equality is the square using the existing canonical
  `comparisonUpperStarCompUpperStarIso`, oriented from pro-etale pullback of comparison
  to comparison of etale pullback.
- Annihilator transitions: the third conjunct quantifies over r≤r' and uses
  `IsFiniteTateEtaleTransition`, whose defining equation sends each root to its
  `l^(r'-r)` power and extends this to the same tensor generators. The unique t is an
  iso and satisfies `mapIso t ≪≫ b_r = b_r'`. This is independence of the etale sheaf
  together with its comparison. Transitions for a common larger exponent compare
  arbitrary choices; their composition and identity laws follow from this equation
  and full faithfulness, rather than being unconstrained choices.
- Uniqueness of descent: the fourth conjunct quantifies over every etale module sheaf
  G and every comparison alpha. It asserts `∃! h : etaleTwist ≅ G` with
  `mapIso h ≪≫ alpha = b`. This retains comparison-preserving uniqueness, not just
  uniqueness of an isomorphism class, for every nonnegative tensor power.
- No divisibility of n by the ramification index: no such binder or hypothesis occurs.

Dependency declarations read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its imported `CoefficientExtension` supplies
  `Padic.coefficientExtensionRing`, its integer ring, ideal and uniformizer.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `proEtaleSiteComparison` and
  `proEtaleSiteComparisonModules`; the latter uses the existing
  `ProEtale.comparisonUpperStar` / `comparisonAdjunction` from
  `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: `etaleFiniteTwistPullback` and
  the publicly imported `finiteEtaleTateTwist`, `finiteEtaleTateOneGenerator` and
  `finiteEtaleTateSheaf`. The nonnegative branch of that signed sheaf is exactly the
  nonnegative twist used here.
- `Sheaf.Paper.CoefficientTwistsDetailed`: `finiteCoefficientTwist`,
  `coefficientTwistPower` and `coefficientTwistLine`. Its all-coefficients package
  `coefficientTateTwists` carries additional global notation irrelevant to this finite
  comparison; the finite specialization is its recorded underlying construction.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`, the
  existing bifunctor used by the finite etale twist dependency and its proof plan.
- `Sheaf.Paper.PurTwistSheafLocallyFree`: `purTwistFiniteOne`, `purTwistIntegralOne`,
  `purTwistIntegralQuotient`, `purTwistIntegralTensor`, `purTwistZlOne` and
  `purTwistForgetPreservesSheafification`.
- `Sheaf.CategoryTheory.ConstantRingModuleSheaves`: `constantRingModuleRestriction`;
  `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`:
  `realizationRingUnit`. The transport composes existing functors rather than copying
  their construction.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`:
  `siteSheafTensorTmul`; Mathlib's `sheafToPresheaf` lax monoidal tensor map is used
  on the module-valued etale side.
- All recorded available proof-dependency modules are imported without `public` unless
  already a statement import. No import cycle was introduced.

Source reading: Stacks `etale-cohomology.tex`, section-kummer (03PK), identifies roots
as the units with the displayed power equation and establishes Kummer local lifting.
`proetale.tex`, section-comparison (099R), lemma-describe-pullback-from-etale (0GLZ),
and lemma-fully-faithful (099T), give the section formula and comparison-unit uniqueness.
The full eight-step node proof is retained as the theorem's natural-language proof plan,
including ordinary quotient tensor reduction without flatness and all pullback steps.

Edge cases checked before and after writing:

- n+1=1 and r+1=1 are included. Arbitrary higher annihilators are included, whether
  or not they are the least annihilator. No e|n requirement appears.
- k=0 uses empty tuples and constant coefficients; normalization is not vacuous,
  since every pro-etale W maps to the terminal etale T. k=1 recovers the first line.
- Empty T is allowed: module sheaves are zero, roots and root-limit sections over
  the empty test are unique, and comparison-preserving iso uniqueness still holds.
- The identity v and arbitrary compositions remain in the pullback quantifier.
  r'=r gives exponent l^0=1 and hence identity transition; common larger annihilators
  give the canonical cocycle by the comparison equation.
- Non-etale W and non-affine, non-quasi-compact T are not excluded. All test objects
  retain the small site's object universe u+1 and morphism universe u.

Searches performed:

- msearch LeanFinder: “Finite coefficient Tate twists descend from the pro-etale site
  to the etale site canonically”: eight hits, mainly etale-site definitions and
  condensed-module constructions; no matching Tate descent theorem.
- msearch Loogle: `AlgebraicGeometry.ProEtale.comparisonUpperStar`: zero Mathlib hits
  (this is a project declaration); its actual upstream definition was read directly.
- msearch LeanSearch: “Finite Tate sheaf on etale site is comparison pullback to
  proetale site”: eight hits, including the generic sheaf inverse image and its
  finite-limit property, but no coefficient-specific Tate descent.
- msearch grep: `Tate|rootsOfUnity` under AlgebraicGeometry: no matching descent theorem.
- Direct rg in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id,
  `finiteEtaleTateTwist|finiteCoefficientTwist|finiteTate.*[Dd]escent`: no match.
  Direct project rg found the recorded etale Tate and coefficient-twist modules, which
  were read and reused. Searches for the proposed theorem/helper names in Mathlib's
  exposed/project name registry `dag/lean_names_upstream.json`, upstream and
  `lean/Sheaf` found no name collision.

Validation: file-only `scompile.py N1 lem-amb-finite-tate-site-descent` compiled the
sandbox and actual module independently. All variables/universes are declared, all
lines are at most 100 characters, and the only postponed theorem is the item itself.
No `STATEMENT-DISPUTED` issue or source-statement defect was found.

## Second reading by N1

A separate second pass reopened the original node and the complete final Lean module.
The pass checked the successor indexing against both existing constructions: n+1 is
exactly the finite quotient exponent in `purTwistFiniteOne`, and the r-th root-limit
projection has exponent l^(r+1). It also checked the order of every comparison square,
the power l^(r'-r), k=0, and the orientation of the unique descent iso.

The reading identified two implementation hazards during drafting and they were fixed:
constant ring sheaves formed before/after forgetting commutativity are connected using
`constantCommuteCompose` and the existing scalar-restriction functor; and natural-number
powers in annihilation hypotheses are cast after exponentiation, matching the recorded
etale interface. It also retained arbitrary pro-etale W in normalization, avoiding a
vacuous condition that would require etale-local infinite root lifts. No hypothesis or
conclusion mismatch remained in this pass. There are no new/dependency modules to review.
