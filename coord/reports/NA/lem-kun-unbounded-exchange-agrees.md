## Worker report

The delivery states `lem-kun-unbounded-exchange-agrees` in
`Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees`. It contains two theorems, each with
proof `sorry`, and two explicit composite isomorphisms for the degree-zero endpoints.
There is no change to the mathematical statement, no new DAG node, and no dependency
record repair. The auxiliary isomorphisms are the canonical endpoint identifications
already specified in this node, not new derived functors or new exchange maps.

Hypothesis and clause correspondence:

- The four schemes and the four arrows are explicitly bound with exactly the directions
  in the node. `sq : ChosenCartesianSquare g' f' f g` retains the chosen Cartesian
  identification as well as the commutativity equation. Both exchanges use
  `sq.toCommSq`, since only that commutativity enters their construction.
- `exactDerivedBaseChangeMap_agrees_plus` binds
  `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`.
  These are the node's bounded below derived abelian sheaves, the integral coefficient
  case, in the encoding explicitly recorded by `def-weil-pbc-derived-categories`.
  No torsion, finite cohomological dimension, geometric property, or extra bound is assumed.
- The unbounded arrow is exactly
  `(exactDerivedBaseChangeMap AddCommGrpCat sq.toCommSq).app K.obj`.
  `K.obj` is the full-subcategory inclusion `iota_X K`.
- The bounded arrow is exactly `derivedBaseChangeMapPlus AddCommGrpCat sq.toCommSq`,
  mapped by `DerivedCategory.Plus.ι.map`. Its source is identified with the unbounded
  source by applying `D(g^*)` to `f_*.rightDerivedFunctorPlusCompatibility.inv.app K`.
  Its target is identified with the unbounded target by
  `f'_*.rightDerivedFunctorPlusCompatibility.hom.app (D+(g'^*).obj K)`.
  The inverse-image comparison `mapDerivedCategoryPlusCompatibility` is `Iso.refl`
  by its actual definition: the restricted functor is literally the full-subcategory
  lift of `iota ⋙ D(u^*)`. Thus the two identity inverse-image comparisons are already
  expressed by definitional equality, not omitted assumptions or chosen identifications.
- The direct-image comparison used here is the library's
  `rightDerivedFunctorPlusCompatibility`, defined by `Functor.rightDerivedUnique` with
  the two right-derived units. Its construction restricts the unbounded derived functor
  to bounded below complexes of injectives and uses that they are K-injective. It is
  the natural comparison computing both functors on the same representative, not an
  existential or an arbitrary objectwise isomorphism.
- `exactDerivedBaseChangeMap_homology_zero` binds an arbitrary
  `Λ : Type (u + 1)` with `[CommRing Λ]` and an arbitrary sheaf
  `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  `DerivedCategory.singleFunctor _ 0` places F in degree zero. This is the landed
  six-functor encoding of constant-ring module sheaves; the coefficient size follows
  the dependency's recorded convention and allows a lift of every smaller ring.
- The first equality in that theorem applies `DerivedCategory.homologyFunctor _ 0`
  to the specified unbounded exchange, and compares it with
  `(baseChangeMap (ModuleCat Λ) sq.toCommSq).app F` via the two fixed endpoint
  isomorphisms. The latter is precisely the module adjunction mate of the termwise
  square comparison followed by the inverse image of the counit, by the definition
  of `baseChangeMap` in `WeilConjectures.SixFunctors.BaseChange.Square`.
- `exchangeSourceZeroIso` is the inverse of the exact inverse-image/cohomology
  comparison, followed by inverse image of
  `homologyRightDerivedFunctorObjSingleFunctorIso F 0` and
  `rightDerivedZeroIsoSelf.app F`. It identifies
  `H⁰(g⁻¹ Rf_* F[0])` with `g⁻¹ f_* F`.
- `exchangeTargetZeroIso` first applies `H⁰ Rf'_*` to the exact inverse-image/single
  comparison `g'^*.mapDerivedCategorySingleFunctor 0`. Then the same two classical
  right-derived comparisons identify `H⁰(Rf'_* (g'⁻¹ F)[0])` with `f'_* g'⁻¹ F`.
  Both definitions have actual composite data and no postponed proof.
- These degree-zero isomorphisms use the existing single-object comparison built from
  the nonnegative injective resolution, and `rightDerivedZeroIsoSelf`, the inverse of
  `toRightDerivedZero` for the left exact functor. Their normalizations are therefore
  those of the augmentations. There is no assertion that all of `Rf_*F[0]` is a
  single sheaf, and no assertion about its positive cohomology.
- The second conjunct applies `moduleAbelianForget Λ Y'` to the normalized degree-zero
  arrow `sourceIso.inv ≫ H⁰(Ex) ≫ targetIso.hom`. It then inserts exactly
  `moduleAbelianLowerStarIso Λ f'` and the inverse `moduleAbelianUpperStarIso Λ g'`.
  The right hand side is the inverse `g` coefficient mate, `g` inverse image of the
  `f` evaluation identity, and `baseChangeMap AddCommGrpCat sq.toCommSq` on the
  forgotten F. This is the node's underlying abelian exchange clause, with the fixed
  coefficient maps of `lem-weil-pbc-module-abelian-underived-exchange`.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare` and its `toCommSq`.
- `Sheaf.AlgebraicGeometry.DerivedCategories` (including its recorded existing
  six-functor encoding): `DerivedCategory`, `DerivedCategory.Plus`,
  `DerivedCategory.homologyFunctor`, and `Etale.DerivedCategoryModule` as the
  module-category interpretation. The bounded-subcategory Mathlib match is
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`:
  `Etale.exactDerivedBaseChangeMap` and `Etale.exactDerivedSquareUpperStarIso`.
  This is the actual recorded canonical mate with exact termwise inverse image;
  the older monoidal-only unbounded interface is not used in its place.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `Etale.derivedBaseChangeMapPlus`, with its resolution computation in the docstring.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryPlus`, `mapDerivedCategoryPlusCompatibility`,
  `mapDerivedCategoryHomologyFunctorIso`; Mathlib's same-topic module supplies
  `mapDerivedCategorySingleFunctor`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.lowerStar`, `Etale.upperStar`, and their canonical adjunction and
  finite-limit/exactness instances. No alternative direct image is constructed.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`:
  `Functor.rightDerivedFunctorPlusCompatibility` and
  `homologyRightDerivedFunctorObjSingleFunctorIso`. The classical
  `Functor.rightDerivedZeroIsoSelf` gives the last degree-zero identification.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`, the recorded constant-ring
  module interpretation. The module-valued sheaf upper/lower-star API realizes that
  interpretation in the project's six-functor encoding; its fixed abelian mates are
  the following already recorded coefficient comparisons.
- `Sheaf.AlgebraicGeometry.ModuleAbelianUnderivedExchange`:
  `Etale.moduleAbelianUnderivedExchange_compatibility`; its imported
  `ModuleAbelianDerivedDirectImageComparison` supplies `moduleAbelianForget`,
  `moduleAbelianLowerStarIso`, and `moduleAbelianUpperStarIso`.
- `WeilConjectures.SixFunctors.BaseChange.Square`:
  `Etale.baseChangeMap`, with its mate definition and transpose formula.

The recorded proof-dependency modules that have declarations are imported without
`public`, including the K-injective, termwise adjunction, derived adjunction, exact
functor, module left-exactness and module-linearity interfaces. The declaration
docstrings carry the complete node proof: same injective representatives and derived
adjunction data for the first clause; the termwise module mate on compatible augmented
resolutions, followed by degree-zero homology and coefficient forgetting, for the second.

Edge cases checked against the signatures and constructions: arbitrary lower bounds of K
(including negative bounds), zero sheaf and zero complex, empty schemes, identity arrows
and identity squares, zero coefficient ring, rings of arbitrary characteristic, and
nonproper/nonflat morphisms. None is excluded. The chosen square is used only through
its commutativity by the maps. The theorem does not incorrectly assume that inverse
image preserves injective complexes, nor that derived direct image is ordinary direct
image in every degree. All variables and universes are explicitly bound.

Searches (2026-10-16):

- `msearch.py leansearch`, query "The unbounded derived base change transformation
  agrees with the bounded below exchange and its zeroth cohomology is the underived
  mate": service unavailable (Internal Server Error); no search verdict assigned.
- `msearch.py leanfinder`, query "The unbounded derived exchange restricts to bounded
  below exchange and zeroth cohomology on a sheaf is underived exchange": eight hits
  about `DerivedCategory.isGE_Q_obj_iff`, `isLE_Q_obj_iff`, their instances, and
  existence of bounded or single-complex representatives. None states this comparison.
- `msearch.py loogle`, query
  "CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso,
  CategoryTheory.Functor.homologyRightDerivedFunctorObjSingleFunctorIso": no hits;
  the service does not know the upstream-only first identifier.
- `msearch.py grep`, query "unbounded exchange" in the six-functor source path:
  zero hits. Second query
  `derivedBaseChangeMap.*(agrees|zero|plus)|exchange(Source|Target)ZeroIso`:
  zero Mathlib hits.
- Direct `rg` in Mathlib, `WeilConjectures`, `lean/Sheaf` and the upstream name table:
  searched `derivedBaseChangeMap`, `rightDerivedFunctorPlusCompatibility`,
  `mapDerivedCategoryPlusCompatibility`, `mapDerivedCategoryHomologyFunctorIso`,
  `mapDerivedCategorySingleFunctor`, and all four proposed declaration names.
  Found and reused the fixed functorial comparisons; no collision for the four names.
  The upstream `DerivedUnbounded.lean` still lists bounded/unbounded compatibility
  as a TODO. `DerivedComparison.lean` compares two bounded maps only.
  A landed `abelianDerivedBaseChangeArrow_eq_plus` concerns the separate
  `abelianDerivedBaseChangeArrow` interface, not this node's recorded
  `exactDerivedBaseChangeMap`. `grep -rn lem-kun-unbounded-exchange-agrees` in the
  upstream sources found no existing declaration.

Validation: `scompile.py NA lem-kun-unbounded-exchange-agrees` compiles the delivered
file both in its isolated sandbox identity and its library module identity, with no
errors or warnings. Only the two requested theorem proofs are `sorry`; definitions
are explicit composites. No statement fault or disputed clause was found.


## Second reading by NA

I independently read the node statement in
`dag/nodes/sec-smooth-purity/lem-kun-unbounded-exchange-agrees.json`, the declarations imported by
the module, and the module signature. The node introduces a cartesian square of schemes with arrows
`f : X ⟶ Y`, `f' : X' ⟶ Y'`, `g' : X' ⟶ X`, and `g : Y' ⟶ Y`; Lean renders these as the four
implicit morphisms and `sq : ChosenCartesianSquare g' f' f g`, which stores the chosen pullback
isomorphism with both projection equations; its `toCommSq` supplies exactly the commutativity used
by both exchange constructions. Verdict: exact objects and square hypothesis.

The node then fixes the recorded derived categories, their bounded-below full subcategories and
inclusions, and an arbitrary `K ∈ D⁺(X_et)` at integral coefficients. Lean renders this as `K :
DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`. The first theorem equates
the unbounded exchange component at `K.obj` with the bounded exchange component transported by the
inverse-image comparison, `DerivedCategory.Plus.ι.map`, and the direct-image comparison. The
displayed composite has exactly the source and target of the node's exchange; the inverse/forward
orientations match the node's `u⁻¹ ι ≅ ι u⁻¹` and `Ru_*^unb ι ≅ ι Ru_*⁺` comparisons. No properness,
torsion, finiteness, characteristic, or boundedness assumption beyond `D⁺` is added. Verdict: all
first-clause hypotheses and comparison data match.

For the second clause, the node quantifies over arbitrary `Λ` with `[CommRing Λ]` and arbitrary `F ∈
Mod(X_et, Λ)`, placed in degree zero. Lean renders this exactly as `Λ : Type (u + 1)`, `[CommRing
Λ]`, and `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, with `DerivedCategory.singleFunctor
_ 0`. The first conjunct applies `DerivedCategory.homologyFunctor _ 0` to the unbounded exchange and
identifies its endpoints through the explicit `exchangeSourceZeroIso` and `exchangeTargetZeroIso`;
it states precisely the module underived `baseChangeMap`. The second conjunct forgets coefficients
and inserts the recorded `moduleAbelianLowerStarIso` and `moduleAbelianUpperStarIso` comparisons,
yielding the abelian `baseChangeMap` on `moduleAbelianForget Λ X`. This is exactly the node's
underlying abelian exchange clause. The theorem does not identify the whole derived direct image
with an ordinary direct image or assert anything about positive cohomology. Verdict: every
second-clause quantifier and equality is present with the required order and coefficient category.

The two endpoint definitions are real composites. `exchangeSourceZeroIso` uses the exact
inverse-image homology comparison, the single-object right-derived comparison, and
`rightDerivedZeroIsoSelf`; `exchangeTargetZeroIso` applies homology to the inverse-image
single-functor comparison and then the same two direct-image degree-zero comparisons. Their source
and target types are the two canonical degree-zero identifications in the node, and their composite
orientation agrees with the theorem equalities. No hollow definition or private replacement of a
dependency notion was found.

I checked edge cases represented by the binders and definitions: identity morphisms and arbitrary
supplied chosen cartesian squares, empty schemes, zero sheaves and zero complexes, arbitrary lower
bounds in `D⁺`, zero coefficient rings where an instance exists, and arbitrary characteristic. The
statement has no nonemptiness, properness, flatness, torsion, finite-generation, or positivity
hypothesis that would exclude a node case. Universes are explicit: scheme and site universe `u`,
coefficient type `u + 1`, and general coefficient category universe `v`; no unbound variable
remains.

Search review: `rg` over the project and slopmaster2 source found the dependency declarations
(`exactDerivedBaseChangeMap`, `derivedBaseChangeMapPlus`, `rightDerivedFunctorPlusCompatibility`,
the homology comparisons, and module coefficient comparisons) but no declaration of either theorem
or either endpoint notion. Searches with `msearch.py` LeanSearch (service unavailable), LeanFinder,
and Loogle found only generic derived-category and mate APIs, not this exchange comparison. Mathlib
and source grep found no matching statement. Thus no existing declaration supersedes this module and
no second definition is introduced.

No mismatch was found between the node and Lean, so no repair was necessary. I verified the file
with `python3 /home/ubuntu/weil-launcher-nt/scompile.py NA lem-kun-unbounded-exchange-agrees
lean/Sheaf/AlgebraicGeometry/UnboundedExchangeAgrees.lean`; both sandbox and library identities
compile cleanly, with only the two theorem `sorry` proofs permitted by stage 2.

 Second-reader source verification: the blueprint source and Stacks `.tex` files are absent from
this read-only local clone, so I read the exact blueprint file and `sites-cohomology.tex` at
`remark-base-change` (07A7), and `derived.tex` at `lemma-left-exact-higher-derived` (05TD), from the
project server read-only. I also checked the published
[07A7](https://stacks.math.columbia.edu/tag/07A7),
[0736](https://stacks.math.columbia.edu/tag/0736), and
[05TD](https://stacks.math.columbia.edu/tag/05TD) texts. The blueprint's same-mate argument is the
source of the first clause; the already reviewed node spells out its ill-typed original sheaf
sentence as a degree-zero statement, consistently with 05TD(3). This delivery makes no further
statement correction. Tag 0736 assumes flat inverse images in the ringed-topos setting; for constant
coefficients the recorded étale inverse images are exact for every scheme morphism, so this imposes
no additional scheme-flatness hypothesis here. Tag 07A7 assumes just a commutative ringed-topos
square; it imposes no Noetherian, properness, or coefficient restriction. Tag 05TD assumes an
everywhere-defined right derived functor and left exactness for its degree-zero identification.
Enough injectives/K-injectives and finite-limit preservation are supplied by the actual imported
sheaf functors, rather than extra statement binders.

Independent second-reader searches (2026-10-16), with different queries from the worker: LeanFinder
via `msearch.py`, “Compatibility of canonical right derived functor base change with degree zero
cohomology and inclusion of bounded below complexes”, returned generic exact-functor localization,
`InjectiveResolution.isoRightDerivedObj`, `rightDerived_map_eq`, and `toRightDerivedZero`, without
either comparison theorem. Loogle query `CategoryTheory.Functor.rightDerivedZeroIsoSelf` returned
that canonical isomorphism and its identities; I opened its dependent single-object comparison in
`RightDerivedFunctor/PlusSingle.lean` and `PlusCompatibility.lean` to verify augmentation
normalization. LeanSearch query “Zeroth cohomology of the total derived base change mate for sheaves
agrees with the original base change morphism” was unavailable (Internal Server Error); no verdict
assigned. Independent `rg` in Mathlib, slopmaster2, and `lean/Sheaf` searched the four declaration
names, `baseChange.*homology`, `exchange.*zero`, and `rightDerivedFunctorPlusCompatibility`; the
hits were existing generic comparison helpers, unrelated affine base change statements, and bounded
base-change cohomology, not the theorem about this recorded unbounded exchange.

I opened `rightDerivedFunctorPlusCompatibility` itself: it is `rightDerivedUnique` for the two
explicitly defined right-derived units, and its instance uses the K-injectivity of bounded below
injective representatives. I opened `mapDerivedCategoryPlus` and
`mapDerivedCategoryPlusCompatibility`: the former is the full-subcategory lift and the latter is
literally `Iso.refl`. Thus omission of identity inverse-image comparison factors from the first
equality is justified definitionally. I opened `moduleAbelianUnderivedExchange_compatibility`,
`moduleAbelianForget`, `moduleAbelianLowerStarIso`, the source definitions of `baseChangeMap` and
`derivedBaseChangeMapPlus`, and `exactDerivedBaseChangeMap`: the module/abelian comparison has
precisely the coefficient-isomorphism orientations used by the second conjunct; the two exchanges
are the fixed mate and resolution-descent constructions, respectively. The node's `lean.statement`
is verbatim equal to the first theorem's signature. There are no new nodes or dependency modules in
this delivery to audit.
