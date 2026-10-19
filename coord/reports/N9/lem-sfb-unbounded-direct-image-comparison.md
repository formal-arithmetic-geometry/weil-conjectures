## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison` as
`AlgebraicGeometry.ProEtale.unboundedDirectImageComparison`. Its statement is unchanged.
The module also constructs `unboundedDirectImagePullbackIso` and
`unboundedDirectImageComparisonMap`, with real definition bodies. Only the final theorem
has a postponed proof. Its docstring follows all twelve steps of the DAG proof.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field is `(k : Type u) [Field k]`; finite or algebraically closed is
  `hbase : Finite k ∨ IsAlgClosed k`.
- The prime is `{ℓ : ℕ} [Fact ℓ.Prime]`; invertibility in k is
  `hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ))`.
- The finite commutative coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  Discreteness is intrinsic to the fixed-ring module-sheaf encoding: no topology or
  completed coefficient object is substituted. Being killed by a power of ℓ is
  `hA : ∃ n : ℕ, (ℓ : A) ^ n = 0`.
- The schemes are `{X Y : Scheme.{u}}`, with `X.Over (Spec (CommRingCat.of k))` and
  `Y.Over (Spec (CommRingCat.of k))`. For each structure morphism, finite type is rendered
  by `LocallyOfFiniteType` and `QuasiCompact`. This is the recorded finite-type interface.
- The morphism is `(g : X ⟶ Y) [LocallyOfFiniteType g] [QuasiCompact g]`. No compatibility
  with the two structure morphisms is assumed: it is not required in the source wording
  or the cohomological-dimension argument.
- Every unbounded K is covered by
  `(K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))`.
  This is definitionally `Etale.DerivedCategoryModule A X` from the recorded derived
  category dependency. There is no boundedness, constructibility, or Tor condition.
- `ν_T^*` is the recorded `comparisonUpperStar (ModuleCat A) T`, descended termwise by
  `mapDerivedCategory`. This is the module left adjoint of the site comparison.
- Both `Rg_*` functors are `(Etale.lowerStar (ModuleCat A) g).rightDerivedFunctor` and
  `(ProEtale.lowerStar (ModuleCat A) g).rightDerivedFunctor`. Their source module defines
  total right derivation by the K-injective derivability structure. No bounded-below
  derived operation appears in the signature or in the comparison-map definition.
- The inverse-image square is the actual `comparisonUpperStarCompUpperStarIso` from
  `sk-thm-pe-direct-image-comparison`. `unboundedDirectImagePullbackIso` applies its
  localization between the two `mapDerivedCategoryCompIso` identifications. Both directions
  are the specified isomorphisms, with no chosen arbitrary isomorphism.
- The last arrow is exactly the counit of
  `(Etale.upperStarLowerStarAdjunction (ModuleCat A) g)
  .mapDerivedCategoryRightDerivedAdjunction`, mapped by `ν_X^*`.
- `unboundedDirectImageComparisonMap` takes that composite through the `homEquiv` of the
  pro-etale `mapDerivedCategoryRightDerivedAdjunction`. It is therefore literally the
  mate prescribed in the node, in the prescribed direction.
- The conclusion is `IsIso (unboundedDirectImageComparisonMap A g K)` for every K,
  asserting invertibility of this particular comparison map.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories` (read with `scompile.py --source`
  because the local older source checkout lacks it): reexports
  `AlgebraicGeometry.Etale.DerivedCategoryModule`; its definition was read in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`. The recorded torsion predicate
  is not needed in the statement because the coefficient ring is already primary.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, `finiteCoefficientRealization`,
  `finiteCoefficientRealizationIsEquivalenceRing`, and `finiteCoefficientComparison`.
  These identify the ordinary fixed-ring module sheaves used here with modules over
  the sheafification of continuous functions on connected components. We reuse its
  fixed-ring sheaf presentation, also used by the recorded bounded-below direct-image
  comparison; we do not define a second module category or a second coefficient sheaf.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules`, whose left adjoint is `comparisonUpperStar`.
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`:
  `directImageComparison` and `directImageComparisonPullbackPlusIso`; its unbounded
  inverse-image-square clause is the composition of the three isomorphisms used here.
  Its bounded-below mate is retained only as a proof input, not the item's map.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, together
  with `QuasiCompact` as the recorded conjunction meaning finite type.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`,
  `Etale.upperStar`, and `Etale.upperStarLowerStarAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the recorded intrinsic
  constant-coefficient operations, reexported by the comparison dependency. Their
  fixed-scalar realization is `ProEtale.upperStar`, `ProEtale.lowerStar`, and
  `ProEtale.upperStarLowerStarAdjunction` from the existing six-functor interface.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`:
  `Adjunction.mapDerivedCategoryRightDerivedAdjunction`. Its exact-left-adjoint interface
  avoids imposing any K-flat/monoidal hypotheses on this ordinary inverse-image functor.
- `Sheaf.CategoryTheory.SfbDerivedCategories`: supplied for the previously unrecorded
  `sk-def-sfb-derived-categories`, as described below.

All stated proof-dependency modules are imported without `public` unless they already
provide a statement dependency. Unrecorded proof nodes have no module to import; they
are not needed to type the statement. The proof docstring names their uses explicitly.

Edge cases checked before finalizing: empty X and empty Y are allowed; the zero ring is
allowed, including exponent n = 0; identity morphisms are allowed; no separatedness is
assumed; K may have nonzero cohomology in arbitrarily high and low degrees. The finite
field branch and algebraically closed branch have exactly the same conclusion. Site
objects live in u+1, site morphisms in u, and coefficient module values in u+1; no site
universe equality or extra size bound is imposed. The auxiliary inverse-image square
and mate are defined even before the field, primary, finite-type, and finiteness
hypotheses are supplied.

Searches for the item and the dependency interface:

- `msearch.py ... leanfinder "unbounded derived direct image comparison from etale to
  proetale finite coefficients"`: eight general etale-site/morphism results, no comparison
  theorem. The full wrapper output was inspected.
- `msearch.py ... loogle "Functor.rightDerivedFunctor, Adjunction.derivedAdjunction"`:
  zero results; the index reports the project-specific identifier unknown.
- `msearch.py ... grep "comparison.*[Uu]nbounded|[Uu]nbounded.*[Cc]omparison"`:
  no Mathlib match.
- `msearch.py ... leansearch "unbounded derived functor adjunction and bounded
  constructible derived category of modules over a noncommutative ring object"`:
  eight results including Mathlib `Adjunction.derived` and `Adjunction.derived'`, scalar
  change adjunctions and general triangulated adjunction structures. None states the
  total-tensor/arbitrary-quasi-isomorphism interface or the pro-etale last table row.
- `rg` for `lem-sfb-unbounded-direct-image-comparison` in the older upstream
  `WeilConjectures` tree: no declaration.
- `rg` for unbounded/direct-image/comparison terms in upstream and `lean/Sheaf`:
  found the existing bounded-below comparison and canonical mate, unbounded-site
  comparison, proper/base-change comparisons, and consumers mentioning this item in
  proof docstrings. None states this all-finite-type unbounded direct-image comparison.
- `rg` for `sfbBoundedConstructible`, `totalTensorQuasiIsoDerivedAdjunction`, and
  bounded-constructible definitions in the permitted trees: the first two names are new.
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory.boundedConstructible`
  requires `IsCommMonObj R`; its signature was read in full. The upstream derived
  adjunction likewise has extra graded-tensor families and monomorphic resolution
  requirements; the corrected total-tensor and quasi-isomorphism interfaces were read.

No statement correction and no disputed mathematical assertion were needed.
Every theorem introduced in this delivery has proof `sorry`.

## Dependency modules

`sk-def-sfb-derived-categories` had no Lean record or Mathlib match. The delivery supplies
`Sheaf.CategoryTheory.SfbDerivedCategories` and changes only its `lean` field. Its core
localization and derived-functor notions already exist and are reexported, not redefined:
`DerivedCategory`, `DerivedCategory.Plus`, `DerivedCategory.homologyFunctor`,
`Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its unit and resolution formula,
`Functor.leftDerivedFunctorFromTotalTensor`, its counit and resolution formula,
`rightDerivedFunctorOfQuasiIsoResolutionsIsoMapDerivedCategory`,
`leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory`, and
`Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`.

Each clause of the dependency is represented as follows:

- Unbounded localization, K-injectivity, bounded-below subcategory, cohomology, and
  Grothendieck K-injective existence are the reexported existing Mathlib/upstream notions.
  The K-injective existence clause applies to every integer-indexed complex.
- The right-derived clause uses exactly a hypothesis that every complex has an arbitrary
  quasi-isomorphism to a K-injective, with no monomorphism assumption. This is the
  recorded corrected `RightDerivedFunctorOfQuasiIsoResolutions` interface.
- The left-derived clause uses exactly the recorded binary-total-tensor K-flat predicate
  and left-derived interface: additive tensor, countable coproducts, exact ordered-integer
  colimits and preservation by both tensor sides, and functorial flat resolutions.
- The two exact-functor clauses are the recorded exact-comparison isomorphisms, imported
  publicly with their respective resolution assumptions retained.
- `totalTensorQuasiIsoDerivedAdjunction` supplies the derived-adjunction clause on these
  same two functors. Every condition of the node is explicit: abelian source and target;
  additive monoidal source; countable coproducts; exact ordered-integer colimits;
  preservation of countable coproducts and those colimits by both tensor sides;
  functorial flat resolutions; additive f and g; the recorded K-flat quasi-isomorphism
  preservation property of f; `adj : f ⊣ g`; and arbitrary K-injective resolutions in D.
  The conclusion is `Nonempty (Lf ⊣ Rg)`. This is a proposition asserting existence of the
  adjunction, not a data definition choosing an arbitrary map or isomorphism. Its
  docstring gives the chain-map, homotopy, roofs, common-refinement, and naturality proof
  from the node. No extra threefold or fourfold tensor hypothesis is imposed.
- Layer A is `DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)`, an application of the
  existing generic definition at the given site and coefficients. Layer B is the same
  generic definition applied to `Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat) R`,
  taking R to be the given pulled-back ring object. No ring construction is changed.
- The last row's `sfbBoundedConstructible R` explicitly requires cohomology vanishing
  outside some finite interval and `IsConstructibleModuleObject R` in every integer
  degree. That existing predicate uses the given finite stratification, transported
  restriction, and arbitrary finite module presentations. `SfbBoundedConstructible R`
  is its `FullSubcategory`, keeping every ambient morphism. No commutativity, constant
  matrix, Noetherian, completion, or flat-resolution condition is put on this definition.
  `HasDerivedCategory.{wC}` is explicit and permits every chosen localization universe.

The existing commutative `boundedConstructible` cannot state the last row for arbitrary
ring objects; this is why the general predicate is supplied rather than that narrower
interface being recorded as a match. Edge cases: zero complexes, empty schemes, empty
stratifications, noncommutative ring objects, and arbitrary coefficient-category object
universe uA are included. The source's symmetric tensor/flat claims are reexported only
under their stated monoidal hypotheses, not asserted for arbitrary noncommutative rings.

The proof import `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian` is omitted because
it overlaps with the upstream `ModuleObjects.Abelian` imported by the actual module-object
constructibility framework. The latter supplies the same ordinary module-object abelian
interface used to type this module. This follows the launcher's duplicate-import rule.
Other recorded proof-module imports are retained.

## Validation

Both delivered modules have been compiled individually through `scompile.py`, including
compilation in dependency order with a private overlay for the new convention module.
The main construction and theorem were clean before the final proof-import pass; the
final dry run below rechecks the complete final packet. All Lean lines are at most 100
characters, auto-implicit arguments are disabled, and all universes are named explicitly.

## Second reading by N9

No independent worker was started: the dispatcher brief explicitly prohibits other agents
and assigns the independent review to the maintainer after delivery. The worker reread
the node, source paragraph, signatures and all definition bodies against the clause list
above. This removed an unnecessary `g.IsOver (Spec k)` binder before recording the final
signature. The final map is the canonical mate, and the final conclusion applies to every
unbounded K, with no additional mathematical hypothesis.
