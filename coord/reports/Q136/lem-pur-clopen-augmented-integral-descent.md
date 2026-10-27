## Worker report

The module `Sheaf.Paper.AugmentedIntegralDescent` states the assigned node, with every
proof `sorry` and real data in its finite restriction helper. The main declaration is
`WeilConjectures.PurityFiniteSetting.augmentedIntegralMembershipBounds`; the complete
statement also includes `augmentedIntegralReductionComparison` and
`augmentedIntegralRoosDescent`, all listed in `lean.declarations`.

Source read: Bhatt--Scholze, *The pro-etale topology for schemes*, printed p. 24,
Proposition 3.5.1(1) and Definition 3.5.2, from the local PDF. Definition 3.5.2 uses
modules over the completed coefficient sheaf and the actual natural quotient maps.
The finite-clopen application and its proof are the assigned node's seven steps.
No statement correction, dependency-node replacement, or new DAG node is needed.

Hypotheses and objects:

- `P : PurityFiniteSetting.{u}` gives the fixed finite-field/algebraic-closure datum,
  prime different from its characteristic, and finite coefficient subextension of the
  fixed algebraic closure. Its irrelevant positive `level` does not constrain the
  tower: all `n : ℕ` below denote exponent `n+1`.
- `X : Over (Spec (CommRingCat.of P.field.k))`, `LocallyOfFiniteType X.hom`, and
  `QuasiCompact X.hom` say precisely finite type over k. No separatedness is assumed.
- `I : Type w`, `Finite I`, `Xi : I → Over ...`, and `j : ∀ i, Xi i ⟶ X` give the
  finite family over k, with independent index universe. `IsOpenImmersion` and
  `IsClosedImmersion` are both required. `hdisjoint` and `hcover` state pairwise
  disjoint images and union equal to the whole scheme.
- The site is Mathlib's `Scheme.ProEt` and `ProEt.topology`, with native object
  universe u+1 and morphism universe u. `scalarReductionSource` uses the published
  completed coefficient sheaf, not a discrete constant integral ring. Module size
  is u+1. Finite coefficients are the existing uniformizer-power quotients.
- `K : DerivedCategory (scalarReductionSource ...)` is arbitrary and unbounded.
  A chosen resolution is expressed by cochain representatives `T L`, `q : T ⟶ L`,
  `IsKFlatResolutionIndependentCoefficients ... q`, and the separate `∀ m,
  IsFlatOnSite (T.X m)` hypothesis. Every object has a representative, and the
  arbitrary-derived-object portion uses functors and natural transformations.

Clauses:

1. `augmentedIntegralReductionComparison` first asserts that restriction of q is
   K-flat and a quasi-isomorphism (`hqr`), with flat terms. Its `β n` are chain
   isomorphisms between the actual `unrestrictedTowerComplex` reductions. The
   formula using `unrestrictedTowerTensorSection` states the precise restriction
   of every sheafified pure tensor. The implementation writes the coefficient
   tensor first, s tensor x; commutativity identifies this with the node's x tensor s.
2. The next two conjuncts explicitly commute with `unrestrictedTowerUnit` and
   `unrestrictedTowerTransition`. The derived tower isomorphism d is the localization
   of β through `mapDerivedCategoryFactors`. Its equation uses exactly
   `canonicalIntegralReductionTowerMap ... q hq`, hence c_n=[q]⁻¹≫[γ_n], with the
   component resolution hqr. Being an isomorphism of towers retains every t_n.
3. The functor isomorphism on `clopenDerivedReductionFunctor` is natural on all
   derived objects and morphisms, including transitions, and its unit equation
   retains the actual c_n. Before scalar restriction, `α` and `δ` give the finite
   chain and derived comparisons. The chain formula normalizes α on every tensor;
   the equation with `unrestrictedTowerResolutionIso` fixes δ by the canonical
   K-flat computation. Thus neither finite comparison is an arbitrary isomorphism.
4. `augmentedIntegralRoosDescent` asserts existence of countable products on the
   global and component categories. Its later product instance binders choose any
   such products, not an added mathematical assumption. The isomorphism α is
   normalized by every `Pi.π`, using a natural tower isomorphism β normalized on
   the quotient units. `Function.Bijective` states δ ↦ (α_i⁻¹≫r_iδ≫σ_i).
   The final iff uses `IsDerivedLimitTriangle` and the actual `Pi.lift` of
   `sfDerivedReductionUnit` on both sides. That definition is distinguishedness
   of the triangle with arrows c, 1-s, δ, so no arrow is forgotten.
5. `augmentedIntegralMembershipBounds` begins with the iff for
   `IntegralOnSlice.IsComplete ... none`, then the iff for `sfIntegralConstructible`,
   then the iff for `finiteTorConstructibleIntegral`. These are exactly the
   recorded integral category predicates, reused without private copies.
6. Its next conjunct fixes arbitrary a≤b and compares support in `Set.Icc a b`
   for every n with support for every i and every n. The next is the identical
   quantifier order for `HasProEtaleTorAmplitude`; the interval cannot depend on n.
7. For component endpoints a,b the extrema are expressed without choosing a
   `Fintype`: A is attained among a and is ≤ every a_i; B is attained among b and
   is ≥ every b_i. On finite nonempty I these are precisely min and max. Both
   support and Tor bounds follow with these endpoints. A separate universal
   clause permits any common larger ordered interval, also covering empty I.
8. The penultimate conjunct says every derived object on an empty component is
   zero. The final conjunct says an empty partition forces X empty, every derived
   object is zero, completeness and both memberships hold, and every positive
   reduction has support and Tor amplitude in [0,0]. The fixed-interval iff clauses
   also imply all other ordered intervals in this case.

Dependency declarations read and used (including their full signatures/docstrings):

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting` and its coefficient data.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `.QuasiCompact`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`, `.Morphisms.ClosedImmersion`:
  `LocallyOfFiniteType`, `QuasiCompact`, `IsOpenImmersion`, `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its public imports:
  `completedIntegralCommRingSheafUnrestricted`, its projections, the finite quotient
  ring sheaves, `integralConstantToCompletionOfUniverses`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` (the underlying
  module categories in scalarReductionSource/Target are these Mathlib modules).
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and `Q`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `IsKFlatIndependentCoefficients`, `IsKFlatResolutionIndependentCoefficients`.
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `IsFlatOnSite`.
- `Sheaf.Paper.IntegralReductionTowerCanonical`: `canonicalIntegralReductionTower`
  and `canonicalIntegralReductionTowerMap`. Its recorded representative maps are
  `unrestrictedTowerComplex`, `unrestrictedTowerUnit`, `unrestrictedTowerTransition`,
  `unrestrictedTowerTensorSection`, and `unrestrictedTowerResolutionIso` from
  `Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionSource`, `scalarReductionTarget`, `scalarReductionExtension`,
  `scalarReductionDerivedExtension`, `scalarReductionDerivedRestriction`.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`.
  `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
  `Sheaf.Paper.FiniteTorAmplitudeSites` reexports
  `Sheaf.Paper.FiniteTorAmplitude.finiteTorConstructibleIntegral` (namespace
  `WeilConjectures`, not a declaration with the module prefix).
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations` publicly reexports
  the ringed definition; the exact older intrinsic finite-coefficient spelling
  used by the recorded integral predicate is `Scheme.HasProEtaleTorAmplitude`.
- `Sheaf.Paper.ClopenRoosIntegralDescent`: the actual site inclusion,
  `clopenConstantMap`, uniquely projection-normalized `clopenCompletionMap`,
  `clopenIntegralRestriction`, `clopenIntegralComplexRestriction`,
  `clopenIntegralDerivedRestriction`, and `clopenDerivedReductionFunctor`.
  These already exist and are reused, never copied. Its older theorems cover parts
  of this item but not its explicit Hom bijection, finite-derived normalization,
  min/max and empty-category clauses together.

The finite helper in this delivery is canonical precomposition followed by scalar
restriction along the existing constant-section map. Its additive/exactness witnesses
are the corresponding clause of node step 1; they are named theorem/projections,
with no sorry in data. There is no independent new mathematical notion.

Proof imports retained: `ProEtaleClopenRingedModuleGluing`,
`ProEtaleFiniteClopenTensorCalculus`, `IntegralReductionTowerWellDefinedUnrestricted`,
and `FiniteClopenConstructibilityBounds`. The proof-only scalar compositor,
strict-tower Roos and unbounded localization nodes currently have no Lean record,
so there is no recorded module for them to import. No missing statement object is
needed from them to state this node. The library's existing ordinary completed
restriction helpers reside in `ClopenRoosIntegralDescent`, whose node is also the
sole downstream citer of this item. A later automatic reverse proof import from
that module to this one must be omitted under stages/2-statements §3(7), because
it would create an import cycle. This delivery changes no downstream node or file.

Searches actually run using msearch.py:

- LeanFinder: “Restriction to a finite disjoint clopen cover commutes with augmented
  derived quotient towers and detects derived completeness and uniform cohomological
  and Tor bounds”. Eight hits: Profinite.NobelingProof.succ_exact, .CC_exact,
  Functor.mapDerivedCategoryFactorsh, .mapDerivedCategoryFactors,
  DerivedCategory.quotientCompQhIso, .isGE_Q_obj_iff, .isLE_Q_obj_iff,
  .exists_iso_Q_obj_of_isGE_of_isLE. None states the assigned conjunction.
- Loogle: `"DerivedCategory", "IsComplete"`: zero hits.
- Mathlib grep via msearch: `(derivedComplete|IsDerivedComplete|adic).*(restrict|clopen|partition)|clopen.*(reduction|complete)`
  in CategoryTheory: zero hits.
- LeanSearch: “Derived completeness and uniform Tor amplitude descend along a finite
  disjoint clopen cover”: eight hits on flat descent, CompleteSpace.sum, clopen
  partitions/covers and finite coproducts of profinite spaces; no match.
- Local rg in the named `lean/WeilConjectures` and `lean/Sheaf` directories, for
  clopen reductions/completeness and all chosen declaration names; no name clashes.
  The exact blueprint id has no upstream declaration. The existing project module
  ClopenRoosIntegralDescent and its helpers were read and reused as described above.

Edge cases checked: singleton I (identity cover); empty components; I empty and
therefore X empty; K=0; reductions at exponent 1; non-flat coefficient quotients;
ramified E; independent cohomological and Tor intervals; bounds [-2,0] and [1,3]
giving [-2,3]; arbitrary unbounded K; arbitrary index universe w. No added
flatness hypothesis on the coefficient quotient, no completed restriction, no
nonempty-index assumption except exactly on the minimum/maximum clause.

## Second reading by Q136

This is the worker's explicit clause-by-clause self-audit, not an independent-agent
review: the dispatcher prohibits starting another agent; independent review is the
maintainer's next step. With the node and module open, I checked the hypothesis and
clause correspondence recorded above. Repairs from this reading: gave q a genuine
cochain target L rather than confusing a derived object with a chain representative;
retained flat terms separately from K-flatness; normalized finite-derived comparison
by its tensor formula and K-flat computation square; wrote transitions at chain level
explicitly; retained the actual first map in both Roos triangles; expressed attained
min/max without assuming a nonempty partition globally; added the empty-category and
[0,0] clauses. All universes and variables are explicit. No source statement change.
