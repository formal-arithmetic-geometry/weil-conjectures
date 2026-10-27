## Worker report

The module `Sheaf.WeilSheaf.NativeInjectiveAdjunctionModel` states every clause of
lem-sf-native-weil-injective-adjunction-model, in three theorem declarations. All
four theorem proofs (including the coefficient sheaf-condition obligation) are
`sorry`. The one definition has real data: it bundles the existing pointwise
locally finite function algebra presheaf as a ring-valued sheaf, using the named
sheaf-condition theorem as its proof field. No statement, dependency list, or
proof plan of the DAG node changes. No independent new notion is introduced.

Hypotheses and objects:

- `k₀ : Type u`, `[Field k₀]`, `[Finite k₀]` are the finite base field.
  `AlgebraicClosure k₀` is the framework's chosen algebraic closure. The geometric
  fibres in every expression are the actual base changes to that closure.
- `l : ℕ`, `[Fact l.Prime]`, `[Fact (ringChar k₀ ≠ l)]` are the prime and the
  characteristic exclusion. The named `hchar` is explicitly included in the
  three model theorems, even where the formulas would type without it.
  `PadicAlgCl l` and its framework topology are the prescribed Omega, not a
  replacement coefficient field.
- `T.Over (Spec (CommRingCat.of k₀))` gives the structure morphism of T.
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` of that morphism say
  exactly that T is a separated finite-type k₀-scheme. Apply the category-model
  theorem separately to X and Y. The two morphism-model theorems retain these
  six assumptions by named `include` declarations.
- `f : X ⟶ Y`, `[f.IsOver ...]`, `[IsSeparated f]`, `[LocallyOfFiniteType f]`,
  `[QuasiCompact f]` give exactly the separated finite-type k₀-morphism.
  The last three are also explicitly included, not silently omitted by Lean's
  section-variable selection.
- `ProEtale.AdicSheaf l (T ↘ Spec ...).geometricFiber` is A_T, literally the
  native module objects over `ProEtale.adicConstantSheaf`; `ProEtaleWeilSheaf`
  is W_T, literally `IsoAlgebra (WeilSheaf.frobeniusPullback ...)` in the
  abelian category. There is no fixed-pair category formed after localization.
- All scheme universes remain `u`; the coefficient and module universe is
  `u + 1`, and the category of native sheaves lives in `Type (u + 2)`, exactly
  as in the recorded framework. The pro-etale site is the existing
  `Scheme.ProEt.topology`, not a category with artificially equated universes.

Clause correspondence, first paragraph:

- `nativeAdicCoefficientRing l T` has presheaf
  `ProEtale.adicFunctionsAlgPresheaf l T ⋙ forget₂ (AlgCat ...) RingCat`.
  On U this is `ULift (PadicAlgCl.locallyFiniteFunctions l U.unop.left)`;
  maps are precomposition. Thus this is precisely B_T with its existing
  pointwise multiplication, not a chosen unrelated ring sheaf. The only
  postponed field is the sheaf condition, named `nativeAdicFunctions_isSheaf`.
  Ring-valued packaging is needed to state the first clause using Mathlib's
  `SheafOfModules`; the internal B already remains the recorded object.
- The first conjunct of `nativeWeilCategoryModel` is the equivalence A_T with
  `SheafOfModules.{u+1} (nativeAdicCoefficientRing l Tbar)`.
  `PreservesFiniteLimits e.functor` expresses preservation of kernels; an
  equivalence preserves all existing limits, so using finite limits here does
  not strengthen the assertion about equivalence.
- Its next two conjuncts are `IsGrothendieckAbelian.{u+1}` for exactly A_T and
  W_T. Their `Abelian` structures are the existing native instances, not
  chosen new structures.
- The next two conjuncts give `Additive` and `IsEquivalence` for exactly P_T.
- `PreservesFiniteLimits` and `PreservesFiniteColimits` of `IsoAlgebra.forget`
  state exactness of U_T; `ReflectsIsomorphisms` states conservativity.
- Its final universal quantifier ranges over all integer-indexed cochain
  complexes J in W_T and supplies I, `r : J ⟶ I`, `I.IsKInjective`, and
  `QuasiIso r`. Mathlib's `IsKInjective` says every chain map from an acyclic
  complex is null-homotopic. There is no bound or monomorphism requirement.

Clause correspondence, underived and homotopy paragraphs:

- `ProEtaleWeilSheaf.upperStar k₀ l f` and `.lowerStar k₀ l f` are precisely
  F₀ and G₀, already defined by the framework's `IsoAlgebra.mapOfNatIso` of
  the actual Frobenius comparisons. The imports retain the framework entry
  module `WeilConjectures.WeilSheaf.LowerShriek`.
- `ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l f` is the specified
  adjunction, not an arbitrary witness. Its occurrence in the signatures uses
  the actual adjunction data. The first two conjuncts of
  `nativeWeilInjectiveAdjunctionModel` assert additivity; the next two assert
  exactness of F₀, equivalently preservation of finite limits and colimits in
  these abelian categories; the fifth is `G₀.PreservesKInjectiveComplexes`,
  which explicitly means termwise G₀ takes every K-injective to a K-injective.
- Its next two universally quantified equations identify the `.hom.f` carrier
  components of the actual unit and counit with those of
  `ProEtale.adicUpperStarLowerStarAdjunction l (geometricFiberMap f ...)`.
  The latter is the actual module inverse/direct image adjunction L ⊣ R.
- Its last conjunct uses the existing `Adjunction.mapHomotopyCategory` of
  this very native adjunction. For every M and I, its `homEquiv` is
  `unit.app M ≫ K(G₀).map a` and its inverse is
  `K(F₀).map b ≫ counit.app I`. This is exactly the two formulas in the
  node, in Lean's left-to-right composition convention. The existing
  homotopy adjunction is natural in both variables and its unit/counit are
  the homotopy classes of the degreewise native unit/counit (see
  mapHomotopyCategory_unit_app_quotient and its counit counterpart).
- The ambient pullback f* = D(F₀) is the existing
  `(ProEtaleWeilSheaf.upperStar k₀ l f).mapDerivedCategory`, exactly the
  ambient functor in the body of `WeilComplex.upperStar`. This paragraph of
  the node is a definition supplied by the framework, and does not require
  a second definition or an additional equality of arbitrarily chosen
  functors. No bounded constructible preservation theorem is asserted here.

Clause correspondence, total right derivation and computation:

- The actual ambient direct image is the existing
  `(ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor`, used by
  `WeilComplex.derivedLowerStar`; its actual comparison is
  `.rightDerivedFunctorUnit`. Its type is exactly
  `K(G₀) ⋙ Q_Y ⟶ Q_X ⋙ Rf_*`.
- The first conjunct of `nativeWeilDerivedDirectImageModel` identifies this
  pair uniquely, preserving the actual comparison, with the recorded
  `rightDerivedFunctorOfQuasiIsoResolutions` and its unit. It quantifies
  over every resolution-existence proof h; those proofs exist by the first
  theorem, so this does not add an existence hypothesis. The recorded
  interface's universal bijection therefore states exactly the requested
  universal property for the actual pair. Its unique unit-preserving
  isomorphism is the standard equivalent expression of being that universal
  pair, not a claim that two independently chosen functors are equal.
- Its second conjunct states `IsIso beta_I` at every K-injective I.
- Its third conjunct supplies an actual isomorphism c for every J, I, r with
  `I.IsKInjective` and `QuasiIso r`, and fixes its hom as
  `Rf_*.map (Q_X.map [r]) ≫ inv beta_I`. The displayed source and target are
  exactly `Rf_*(Q_X J)` and `Q_Y(G₀ I)`. Here `Q_X` is `DerivedCategory.Qh`
  on the homotopy category; applying it to a complex means first applying
  `HomotopyCategory.quotient`. This is the node's c_r formula with the
  implicit homotopy quotient written explicitly.
- Its fourth conjunct quantifies over arbitrary homotopy morphisms v between
  the images of K-injective complexes I and I' and states
  `beta_I ≫ Rf_*.map (Q_X.map v) = Q_Y.map (K(G₀).map v) ≫ beta_I'`.
  Reversing the written order for right-to-left mathematical composition
  gives precisely the final displayed equation in the node. All maps are
  in the ordinary unbounded derived category of W_Y.

Dependencies read and used:

- def-sf-native-weil-derived-framework:
  `WeilConjectures.WeilSheaf.LowerShriek`, primary entry
  `AlgebraicGeometry.WeilComplex.derivedLowerShriek`; its public imports give
  `ProEtale.AdicSheaf`, `adicConstantSheaf`, `WeilSheaf.frobeniusPullback`,
  `ProEtaleWeilSheaf`, `.upperStar`, `.lowerStar`, and the actual ambient
  `mapDerivedCategory` and `rightDerivedFunctor` in the bodies of the
  restricted operations. I read these native declarations and their docs.
- def-sfb-right-derived-functor:
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`,
  `rightDerivedFunctorOfQuasiIsoResolutionsUnit` and the accompanying
  universal-property and uniqueness declarations. The direct-image-model
  theorem uses this interface explicitly without redefining right derivation.
- def-sp-grothendieck-abelian is the Mathlib leaf:
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`,
  `CategoryTheory.IsGrothendieckAbelian`, read at its full signature and
  universe documentation. The native instances use its size u+1.
- The existing native adjunction and carrier lemmas are in
  `WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction`;
  degreewise and homotopy adjunction data and their quotient normalizations
  are in `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
  The K-injective preservation class is in
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- Recorded proof dependency modules imported for stage 3:
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`,
  `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`,
  `Sheaf.CategoryTheory.FixedPairDerivedForgetComparison`,
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`,
  and the Comp module above. Other recorded proof interfaces are already
  publicly imported by these/the native framework: IsoAlgebraAdjunction,
  ExchangeMate, KInjectiveTotalDerived, and the Mathlib exact derived and
  triangulated homotopy constructions. The proof dependency
  lem-sf-fixed-pair-created-abelian-structure has no recorded Lean interface
  locally; no missing interface is needed to state this item, and no proof
  is attempted. The actual native IsoAlgebra structures are already present.

Sources and edge cases:

- Read local Stacks `derived.tex`, lemma-adjoint-preserve-K-injectives
  (08BJ), and `injectives.tex`, theorem-K-injective-embedding-grothendieck
  (079P), remark-existence-D (079Q). Read the current blueprint
  `latest/blueprint/sec-six-functors/sk-thm-sf-package/` proof of
  fix-lem-tensor-adjunction, step 1, its final Hom bijection. These support
  exactly the native ambient stage and not an unproved restriction to a
  bounded constructible category.
- The empty scheme is allowed; nothing requires a point or a nonzero
  coefficient section. The zero complex is included and is K-injective.
  Complexes may be unbounded in both directions, and arbitrary integer
  degrees, including zero and negatives, remain available.
- The identity morphism, zero maps, nonmonomorphic quasi-isomorphic
  resolutions, and arbitrary homotopy classes between resolutions are all
  admitted by the signatures. The adjunction formulas require no
  K-injectivity; only the specified derived computation uses it.
- The ring helper uses the full underlying space of each actual pro-etale
  test object via the native locally finite function algebra. There is no
  replacement by finite-image or globally finite-dimensional functions.
- No extra universe equality, exactness hypothesis, injectivity hypothesis,
  or hypothesis of existing resolution data has been imposed.

Searches made before writing:

- `msearch.py ... leanfinder` query: "Native Weil underived adjunction exact
  inverse image direct image K injective total right derived computation".
  Eight results, headed by CategoryTheory.Adjunction.derivedε and related
  generic derived-adjunction declarations; none states this native package.
- `msearch.py ... loogle` query:
  "CategoryTheory.Adjunction, CategoryTheory.IsGrothendieckAbelian".
  One result, IsGrothendieckAbelian.tensorObjPreadditiveCoyonedaObjAdjunction;
  no native match.
- `msearch.py ... grep` query:
  "upperStarLowerStarAdjunction|rightDerivedLowerStar|KInjective" in
  CategoryTheory. Four Mathlib hits, all injective Ext imports/usages;
  no native package.
- `msearch.py ... leansearch` query: "Module objects over a sheaf of algebras
  in sheaves of vector spaces are equivalent to sheaves of modules over the
  sheaf of rings". Eight results on Scheme.Modules, SheafOfModules and its
  basic declarations; no equivalence with the native internal B-modules.
- `msearch.py ... loogle` query:
  "CategoryTheory.Adjunction.mapHomotopyCategory"; the installed native
  homotopy-adjunction source was also found by direct project grep and used.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for nativeWeil,
  native_weil, injectiveAdjunction, and the exact node ID found only other
  native comparison modules. The node ID has no existing theorem.
- Additional focused `rg` in both trees for AdicSheaf equivalences,
  adicFunctionsAlgPresheaf, adic ring/sheaf packaging, SheafOfModules and
  mapHomotopyCategory found the actual algebra presheaf in Adic/Ring.lean
  and the existing homotopy adjunction. The general internal-abelian-sheaf
  equivalence module applies to Ab, not to the native Omega-linear internal
  modules, and does not already state the required native equivalence.
  The native category and functor definitions were reused, not duplicated.

No STATEMENT-DISPUTED flag or source correction is needed.

## Second reading by N0

This is a second pass by the dispatched worker, not a claim that another agent
reviewed it: the dispatcher expressly forbids starting other agents, and the
maintainer performs the independent review of the delivery.

With the node and file open, I checked all four paragraphs against the mapping
above. The initial draft would have let Lean omit the separated finite-type
section instances because the existing native functors are more general. I
named and explicitly included all nine such instances and the characteristic
exclusion before the final compile. This preserves the node's hypotheses.

I checked the ring-valued helper against the actual AlgCat-valued locally finite
function presheaf and checked that the equivalence uses the same geometric
fibre as the internal coefficient. Its data contains no sorry. I checked that
the universal property refers to the actual framework rightDerivedFunctor,
with a unit-compatible identification with the recorded dependency, and that
the resolution quantifier has no Mono condition. I checked both orientations
of the homotopy transpose and both displayed derived equations against the
node, using Lean's left-to-right composition. The maps in the final formula
are arbitrary homotopy classes, not just maps of complexes before quotienting.

The first compiler run passed. The final compiler run includes the explicit
hypothesis-retention changes. Final preflight and delivery are recorded by the
prescribed delivery wrapper.
