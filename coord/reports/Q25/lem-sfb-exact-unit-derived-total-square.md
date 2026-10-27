## Worker report

The delivery states `CategoryTheory.exact_unit_derived_total_square` in
`Sheaf.CategoryTheory.ExactUnitDerivedTotalSquare`. Its sole postponed theorem has `sorry`.
All helper definitions have actual data. `ExactUnitDerivedTotalSquare` packages this node's
clauses, using the existing `NonnegativeDerivedTotalizationComparison` throughout. There are
no new nodes, dependency repairs, statement corrections or disputed statements.

Hypotheses and conventions:

- A, B, C have independent object, morphism and localization universes `uA,vA,wA`,
  `uB,vB,wB`, `uC,vC,wC`. They have `Category`, `Abelian`, `HasDerivedCategory` and the
  theorem's `IsGrothendieckAbelian` instances. K-injective-resolution instances used by
  the dependency's `rightDerivedFunctor` are available for Grothendieck categories;
  the ambient derived categories are the ordinary unbounded localizations.
- G is `(G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G]`. H and P additionally
  have `PreservesFiniteColimits`, precisely exactness between abelian categories.
- The specified transformation is `(θ : 𝟭 A ⟶ H)`; no adjunction or additional property
  of this transformation is assumed.
- Every K is `CosimplicialObject (CochainComplex A ℕ)`: SimplexCategory is the category
  of finite nonempty ordered sets and monotone maps, with all cofaces and codegeneracies.
  The existing `nonnegativeCosimplicialTotal` uses alternating cofaces and the signed
  first-quadrant total. `nonnegativeComplexLocalization` extends by zero to Z then uses Q.
- M ranges over `DerivedCategory A`; a is an isomorphism to the localization of this total.
  These parameters are universally quantified in `localized_unit`, `square`, `naturality`
  and the postcomposition clauses, rather than fixed when the record is constructed.

Clause-by-clause correspondence:

1. `exactUnitCosimplicialMap H θ K` is the actual strict map e. It uses Mathlib's
   `NatTrans.mapHomologicalComplex`, the canonical identity comparison and whiskering by K.
   `strict_components` asserts exactly `e[n,q] = θ[K[n,q]]`. Naturality of this strict
   natural transformation includes every simplex operator, and its components are chain maps.
2. `comparisonH.beta K` is E. Its summand characterization is inherited from
   `NonnegativeDerivedTotalizationComparison.beta_summand`, fixing the canonical finite-sum
   identification, rather than an arbitrary isomorphism. `total_unit` is E θ_TK = T(e).
3. `thetaD` is an actual natural transformation `𝟭 (DerivedCategory A) ⟶ H.mapDerivedCategory`.
   `thetaD_unbounded` normalizes it on Q of every Z-indexed complex; localization uniqueness
   therefore determines it. `thetaD_normalized` gives the nonnegative version with the exact
   extension/localization comparison. `localized_unit` is the displayed identity for M,a,
   including the required exact-descent identifications.
4. `comparisonG`, `comparisonH`, `comparisonP` are the recorded normalized derived-total
   comparisons. `compatible` supplies resolutions R of K and T of HK with an actual strict
   g and the equation `R.augmentation ≫ g = e ≫ T.augmentation`. HK is resolved independently;
   H of an injective resolution is never asserted injective. `compatible_augmented` additionally
   resolves X, HX and the strict augmentation simultaneously. It includes quasi-isomorphisms,
   termwise injectivity and all three commuting augmentation/unit equations.
5. `exactPostDerivedTotalComparison` defines u by P_D applied to `RG.mapIso a ≪≫ chi K R`,
   followed by `exactFiniteTotalLocalizationIso P`. The latter is the canonical exact descent
   followed by Q of beta_P. The w in `square` is exactly the same definition for HK,T,H_D M
   with input `H_D(a)`, the exact descent isomorphism and Q(E). `square` is precisely
   `P_D RG(θ_D,M) ≫ w.hom = u.hom ≫ exactPostResolvedTotalMap G P g`.
   The target totals are Q T(P G R) and Q T(P G T), actual coherently resolved diagrams.
6. `column_square` identifies every component of g after G and P with the image of θ_D on
   QK[n], using `comparisonG.column` and the exact descents. Thus the bottom arrow in `square`
   really is the totalized columnwise derived transformation from the node, not an arbitrary
   map between isomorphic objects. Both horizontal arrows are genuine derived isomorphisms.
7. Resolution independence uses the inherited `comparisonG.unique` and `normalized` clauses,
   and the summand-normalized beta. For two choices the canonical identification of their
   resolved targets is the first normalized comparison inverse followed by the second.
   For every compatible strict comparison, `naturality` identifies its actual map with this
   canonical choice identification. Its specialization to m = identity and a = b gives
   independence; its general form is naturality for K,M,a with exactly the required condition
   `m ≫ b.hom = a.hom ≫ QT(f)`. Applying it to HK covers w too. Naturality of thetaD makes
   the vertical arrows commute with these same changes.
8. The inherited `comparisonG.augmentedReplacement` and the explicit
   `compatible_augmented` retain the specified augmentations, including their actual maps.
   `augmentation` displays the equality after P_D: its a and aI are constrained by
   `IsNonnegativeTotalAugmentation`, so they use the degree-zero cosimplicial component,
   zero in higher columns. eX is normalized by the actual resolution r and the derived unit.
   The equality is the actual composite with the totalized columnwise augmentation. The
   quantification covers HK and its H-image augmentation as well as K; composition with a
   or a preceding augmentation into M preserves these equalities by functoriality.
9. Every complex in a total has natural indices. After resolving an internal complex its
   internal total has q,s >= 0, so the outer total contributes exactly n+q+s=r. Both totals
   use the existing finite-diagonal total functor; no infinite product is present. Degree zero
   has only the (0,0) summand, and negative degrees are supplied by extension by zero.
10. `postcomposition` quantifies over a further arbitrary Grothendieck abelian D with independent
    universes uD,vD,wD and exact additive S. It supplies the normalized comparisons cS,cPS.
    Its first equation identifies beta_SP with S(beta_P) followed by beta_S, including the
    canonical termwise composition isomorphism. Its second equation equates the direct SP
    comparison (transported by `mapDerivedCategoryCompIso` and the termwise composition
    isomorphism) with `exactFurtherPostDerivedTotalComparison`. The latter is DEFINED by
    applying S_D to u or w and moving it inside the finite total. Its last equation is the
    entire image square with the actual threefold termwise bottom map. Applying S_D to the
    normalized augmentation and naturality equalities retains their actual maps; the beta
    equation identifies them with the SP equations, including the degree-zero inclusion.
11. The slice restriction instance is obtained by taking S to be the actual
    `SheafOfModules.overFunctor` with ring `R.over U`. Its exactness is the imported
    `localizedSystemExact` / `localizedSystemRestriction*` API (its restriction is definitionally
    overFunctor after forgetting the commutative ring). This is an instance of the quantified
    exact-postcomposition clause, with no condition concerning preservation of injectives.
    No such preservation instance for H, P, S occurs anywhere in the signature.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`:
  `CategoryTheory.IsGrothendieckAbelian` (the exact Mathlib match of def-sp-grothendieck-abelian).
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` and
  `Mathlib.CategoryTheory.Limits.Preserves.Finite`: `Functor.Additive`,
  `PreservesFiniteLimits`, `PreservesFiniteColimits`, the exact functor notions of
  def-sp-left-exact-additive. Composition evidence uses the existing
  `comp_preservesFiniteLimits` and `comp_preservesFiniteColimits` inside a definition only.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded convention
  interface for sk-def-sfb-derived-categories, publicly imported by the totalization dependency.
  As that dependency does, the actual Grothendieck right-derived functor is the existing
  `Functor.rightDerivedFunctor` with its K-injective unit, from
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`.
- `WeilConjectures.CategoryTheory.DoubleComplexTotal` and the Mathlib total API:
  `HomologicalComplex₂.totalFunctor`, `ιTotal`, with natural-index finite totals provided by
  `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`. The recorded definition node's
  module is publicly imported by NonnegativeDerivedTotalization.
- `Sheaf.CategoryTheory.NonnegativeDerivedTotalization`: `nonnegativeCosimplicialTotal`,
  `nonnegativeComplexLocalization`, `NonnegativeCosimplicialResolution`,
  `NonnegativeDerivedTotalizationComparison`, `nonnegativeRightDerivedUnit`,
  `IsNonnegativeTotalAugmentation`, `nonnegative_derived_totalization`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: `Functor.mapDerivedCategory`,
  `mapDerivedCategoryFactors`, the exact mathlib_match of
  lem-weil-pbc-exact-functor-derived-factorization.
- `Mathlib.CategoryTheory.Localization.Predicate`: `Localization.liftNatTrans`,
  `liftNatTrans_app`, `natTrans_ext`, the exact matches of the localization proof dependency.
  The proof plan uses these for thetaD, which the record fixes by its full normalization.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryCompIso`, the canonical exact composition identification.
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap`:
  `HomologicalComplex.mapExtendIso`. `Mathlib.Algebra.Homology.Additive`:
  `NatTrans.mapHomologicalComplex`, `Functor.mapHomologicalComplexIdIso`,
  `Functor.mapHomologicalComplexCompIso`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the existing general-site module convention. `Mathlib.Algebra.Category.ModuleCat.Sheaf.
  PushforwardContinuous`: `SheafOfModules.overFunctor`, `over`, `overMap`, with ring `R.over U`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems` (plain proof import):
  `SheafOfModules.localizedSystemExact`, `localizedSystemRestriction`, and its three
  additive/finite-limit/finite-colimit instances. This supplies the stated slice application.
- def-weil-size-convention is a metatheoretic convention record: the explicit independent
  universes and ordinary derived categories implement it; it has no module to import.

The proof dependency lem-sfb-cosimplicial-injective-total-replacement has no Lean record,
Mathlib match or source declaration, and so has no import to add. Its needed replacement
and strict-map interface is already supplied by the recorded totalization comparison,
whose proof plan imports the functorial bounded injective-resolution construction. No
unstated prerequisite is assumed as a hypothesis and no duplicate notion is introduced.

Source check: read `literature/stacks-project/derived.tex`, lemma-right-derived-exact-functor
(Tag 015F): an exact functor sends quasi-isomorphisms to quasi-isomorphisms and needs no
resolution. The remaining finite-total argument is the seven-step agent argument in this
node, reproduced step by step in the theorem docstring. The current blueprint's
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.proof.md` was also read.

Edge cases checked before finalizing: zero categories and zero diagrams; theta zero or identity;
H,P,S identity functors; a nontrivial derived isomorphism a; the (0,0) diagonal; extension by zero
in negative degrees; degenerate simplex operators as well as cofaces; an arbitrary augmentation
complex in degree zero or in higher degrees; unrelated exact functors which do not preserve
injectives; and unequal object, morphism and localization universes. There is no empty simplex
object, as Delta in the statement consists of nonempty ordered sets. No finite-bound hypothesis
on the whole complex or cosimplicial direction was added.

Searches made with the prescribed msearch tool:

- LeanFinder: `exact natural transformation commutes with derived finite totalization and exact
  postcomposition`: eight results, including `Abelian.Ext.mapExactFunctor_hom`, localization
  derivability/Guitart-exact results and `Functor.mapDerivedCategoryFactorsh_hom_app`.
  None states the normalized finite-total square with its augmentation and postcomposition clauses.
- Loogle: `Functor.mapDerivedCategory, NatTrans.mapDerivedCategory`: zero results, with the
  service reporting unknown identifier `Functor.mapDerivedCategory`.
- LeanSearch: `An exact natural transformation commutes with right derived finite totalization
  after exact postcomposition`: eight results about right-derived natural transformations,
  degree-zero derived functors and Kan extension postcomposition; no finite-total square.
- Mathlib grep: `mapDerivedCategory|mapBicomplex` in Algebra/Homology/DerivedCategory:
  ten results in exact-functor descent and Ext maps. Used its canonical descent API.
- Mathlib grep: `(derived.*total|total.*derived|mapTotalIso)` in Algebra/Homology:
  four results concerning factorization and bounded-below total right derivation; no match.
- Project rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `exactUnit|ExactUnit|derivedTotalSquare|DerivedTotalSquare`,
  `lem-sfb-exact-unit-derived-total-square|nonnegative-derived-totalization|cosimplicial-injective-total-replacement`,
  plus grep for the exact item id in `lean/WeilConjectures`: no existing statement of this node.
  The CechLocalizationUnit module has a downstream, specialized unit map and Cech result;
  it is not this general statement and is deliberately not imported to create a cycle.
  Further searches for total-functor comparisons found the upstream `mapTotalIso`, but the
  node already has the summand-normalized beta in its dependency and that interface is used.
  Existing helper names were searched before choosing the new node-owned names.

Validation: the complete module is compiled by the prescribed scompile.py against the live
published library in module mode; no Lean errors or warnings. The dry run and final delivery
results are supplied by deliver2.py. The sandbox node changes only `lean`; the natural-language
statement, dependency lists, proof and every other field remain verbatim.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
