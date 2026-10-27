## Worker report

The module Sheaf.Paper.BoundedFlatPullbackTest states the unchanged node as
AlgebraicGeometry.ProEtale.BoundedFlatPullbackTest.bounded_flat_pullback_test.
Its only postponed proof is that theorem. The four real-data helpers package the
full domain and the actual termwise, ordinary tensor, and derived tensor functors;
none chooses an arbitrary map or constructs a new tensor or module category.
No new nodes, dependency repairs, statement correction, or disputed statement.

Hypothesis and clause correspondence:

- `V X : Scheme.{u}` and `f : V ⟶ X` give any scheme morphism. No property of
  either scheme or of f is assumed.
- `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]` give the finite commutative
  coefficient ring. There is no topology assumption. A finite ring of any
  initially chosen size admits this presentation; the size convention places
  module values in u+1 while the original site retains object universe u+1 and
  morphism universe u. No equality between those site universes is imposed.
- `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)` is the existing
  fixed-ring presentation of A_X-module sheaves, also used by the dependency's
  recorded derivedTensor. An A-linear sheaf has an action of the constant
  presheaf, uniquely extended over its sheafification, hence is exactly a module
  over the constant ring sheaf. This presentation permits all such module
  sheaves, including the zero ring and the empty scheme.
- `c d : ℤ`, `_hcd : c ≤ d`, and `P : (flatInterval X A c d).FullSubcategory`
  give exactly the specified complexes. Its predicate is the conjunction of
  `∀ q, exactFunctor _ _ (tensorRight (P.X q))` and
  `∀ q, q < c ∨ d < q → IsZero (P.X q)`. These are the precise defining flatness
  and degree-support conditions. A morphism in this full subcategory is every
  chain map between such complexes; it has no extra compatibility requirement.
- `termwisePullback f A` applies the existing `ProEtale.upperStar` termwise.
  This is the recorded `Scheme.proEtaleSheafInverseImage` specialized to
  ModuleCat A: both definitions are left Kan extension followed by
  sheafification along the same `Over.pullback @WeaklyEtale ⊤ f`. The upperStar
  spelling makes its existing additivity and exactness instances available,
  without an added hypothesis or an extra exactness theorem.
- The first conjunct gives flatness of every pulled-back term, zero terms
  outside the same interval, and quasi-isomorphism K-flatness of the resulting
  complex. `(HomologicalComplex.quasiIso _ (.up ℤ)).kFlat` is the recorded
  def-pc-kflat-complex interface for fixed-ring sheaves; preserving
  quasi-isomorphisms by tensor is equivalent to preserving acyclicity (apply
  tensor to a map from zero; conversely use its cone). Both tensor sides are
  included by the existing symmetric monoidal predicate.
- The second conjunct is a natural isomorphism of functors on the full category
  of these P: `Q(f_A^*P) ≅ D(f_A^*)Q(P)`. It has the displayed orientation.
  `mapDerivedCategory` is the ordinary unbounded exact-functor localization,
  not a bounded derived category or an assumed equivalence.
- `derivedTests` is the product of that derived pullback and Q(M[0]), followed
  by the recorded `ProEtale.derivedTensor`. `strictTests` is the product of
  termwise pullback and M[0], followed by the ordinary cochain-complex tensor.
  The latter is Mathlib's signed direct-sum total tensor `mapBifunctor`.
- The third conjunct is `Nonempty (derivedTests ≅ strictTests ⋙ Q)`. A single
  natural isomorphism on the PRODUCT category asserts compatibility with all
  chain maps P→P' and all maps M→M', simultaneously. It is stronger than a
  list of unrelated object isomorphisms only in the way explicitly demanded by
  the word “natural” in the node. No target module is required to be pulled back.
- The last conjunct quantifies `M` over the whole target module-sheaf category,
  and every integer n outside [c,d]. It gives both IsZero of the ordinary
  tensor's degree-n TERM and IsZero of the derived test's n-th cohomology sheaf,
  using the recorded `DerivedCategory.homologyFunctor`.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and ProEt.topology.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: constantSheaf, sheafification of
  the constant presheaf; realized in the fixed-ring sheaf presentation above.
- Sheaf.CategoryTheory.RingedSiteModules: ringedSiteModules is transparently
  SheafOfModules, the intrinsic presentation of the same module-sheaf notion.
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage: proEtaleBaseChange and
  proEtaleSheafInverseImage; read their definitions, source and adjunction.
  The equivalent fixed-ring upperStar is publicly supplied by the existing
  WeilConjectures finite-coefficient Tensor import.
- Mathlib.Algebra.Homology.HomologicalComplex: CochainComplex.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite: IsFlatOnSite and its
  recorded underlying predicate CategoryTheory.exactFunctor, used directly
  for the fixed-ring sheaf tensor as explicitly permitted by this lean record.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory and Q.
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients: the recorded public
  MorphismProperty.kFlat interface, needed for the fixed-ring presentation.
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor:
  ProEtale.derivedTensor; its existing monoidal complex tensor is exactly
  HomologicalComplex.mapBifunctor with curriedTensor.
- Mathlib.Algebra.Homology.DerivedCategory.HomologySequence:
  DerivedCategory.homologyFunctor (the cohomology dependency's Mathlib match).
- Plain proof imports retain the published modules of
  prop-weil-pbc-proetale-constant-exact,
  lem-weil-pbc-ringed-topos-flat-module-pullback,
  lem-pc-bounded-above-flat-kflat-site, and
  lem-weil-derived-tensor-resolution-independent. The exact-functor factorization
  is Mathlib's Functor.mapDerivedCategoryFactors, publicly imported since its
  mapDerivedCategory is also used in the signature. The tensor-complex proof
  dependency is Mathlib's mapBifunctor, already supplied by the complex tensor.
  These are proof inputs, not additional hypotheses of the statement.

Sources read: sites-modules.tex lemma-pullback-flat (05VD), sites-cohomology.tex
lemma-bounded-flat-K-flat (06YQ), the signed total tensor and the existing
resolution-independent construction, plus the main-20261015 blueprint proof of
thm-exc-explicit-preservation paragraph 2. They give exactly this flat-model
calculation. The theorem docstring includes the node's five proof steps.

Edge cases checked before drafting: c=d (one term), zero P, zero M, A=0, V empty,
f the identity, arbitrary non-etale f, and A=Z/4 with M=Z/2. In the latter case M
need not be flat; only the first factor is K-flat, so the ordinary tensor remains
valid. Nothing assumes M descends from X. In all cases strict tensor with M[0]
has only the (n,0) summand in degree n, establishing precisely the requested
interval calculation without requiring a flat second factor.

Searches actually run:

- msearch leanfinder: “A bounded flat complex of sheaves pulls back to a bounded
  K flat complex computing derived tensor with any target sheaf”: eight hits,
  on ordinary module tensor exactness and representably flat site pullback;
  none states this node.
- msearch loogle: “CategoryTheory.MorphismProperty.kFlat,
  CategoryTheory.exactFunctor”: zero hits, unknown kFlat identifier in that
  Mathlib-only service; upstream kFlat was found and read directly.
- msearch grep: “KFlat|kFlat|bounded.*flat”, CategoryTheory: zero hits.
- rg on both lean/WeilConjectures and lean/Sheaf for bounded flat pullback,
  boundedFlatPullback and flatIntervalComplexes: scheme O_X pullback theorems
  and applications, no existing full statement of this node. Read the nearby
  BoundedFlatTensorContinuity module; it concerns condensed coefficients and
  continuity cocones, not this assertion. No duplicate was introduced.
- grep for this exact node id in lean/WeilConjectures and rg in
  dag/lean_names_upstream.json: no match. Every new full declaration name was
  also absent before the sandbox module was written.

Validation: the first server compile diagnosed an unconstrained ModuleCat
universe and additivity inference through the generic inverse-image abbreviation.
Explicit ModuleCat.{u+1} and the definitionally identical upperStar resolve both,
without a new mathematical assumption. The next compile passed elaboration and
library compilation, reporting one overlong line; that line was wrapped. Final
clean compile and delivery preflight are run through the required wrappers.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
