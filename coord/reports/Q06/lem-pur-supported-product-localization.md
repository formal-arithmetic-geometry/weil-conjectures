## Worker report

Item: lem-pur-supported-product-localization. Group Q06, stage 2. This delivery states the two localization-triangle assertions, their coefficient naturality and their open-restriction naturality. The main module is `Sheaf.AlgebraicGeometry.SupportedProductLocalization`; the first declaration is `AlgebraicGeometry.Etale.supportedProductLocalizationFirst`. No theorem is proved: every postponed mathematical proof is a named theorem with `sorry` and a source/proof docstring. Definitions contain constructions, or choice from a uniqueness theorem that determines the map used downstream.

Hypothesis-by-hypothesis correspondence (both main triangle assertions):

* Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
* Finite commutative coefficients: `(A : Type (u + 1)) [CommRing A] [Finite A]`. This is the existing small-etale coefficient convention, allowing every finite ring, including the zero ring, through an equivalent universe lift.
* Schemes over k: `X Y : Scheme.{u}` and the two structure morphisms `f`, `g` to `Spec (.of k)`. These explicit maps are also the arguments of the recorded exterior-product construction.
* Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]` and the corresponding two instances for g, exactly the conjunction recorded by def-weil-finite-type-morphism.
* Separated in the diagonal sense: `[IsSeparated f] [IsSeparated g]`. Properness and universal closedness are not assumed.
* Closed B,C in X and D in Y: morphisms b,c,d and their three `IsClosedImmersion` instances. For the second assertion, b is the node's D' in X, d is B' in Y and c is C' in Y.
* U=X minus C, or V=Y minus C': the actual `c.openComplement`, its inclusion, and `supportOnOpen` (a fibre-product closed immersion).
* K,L in D+: `DerivedCategory.Plus (Sheaf ... (ModuleCat.{u + 1} A))`, with `.obj` used in the recorded unbounded derived category.
* F bounded below: `_hF : ∃ n : ℤ, (externalProduct ... f g K.obj L.obj).IsGE n`. The object is exactly the existing derived external product of the two projection pullbacks, with the existing derived tensor.

Clause-by-clause correspondence:

* `supportedFirstLocalizationSource` is `(tensorRight (RΓ_D L)).mapTriangle.obj` applied to the actual normalized support triangle for X,B,C,K. `supportedFirstLocalizationTarget` is the support triangle for the product support b times d and cut c times Y, with coefficient F.
* The two `distTriang` conjuncts say exactly that these source and target rows are distinguished triangles in `DerivedCategory (ModuleCat A)`.
* The existential triangle morphism has all three components prescribed by equalities. Component 1 is `supportedExteriorProduct` for B intersection C and D, followed only by the support-complement identification. Component 2 is `supportedExteriorProduct` for B and D. Component 3 is `supportedExteriorProduct` on U times Y with restricted K, followed by the inverse canonical identification of that open product with the third target ambient. Thus no arbitrary completion of the first two components is used.
* `TriangleMorphism.comm₁`, `.comm₂` and `.comm₃` impose all three squares, including the boundary square. `mapTriangle` uses the global derived tensor `CommShift` from `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`. For tensorRight its complex representative sends x tensor y to x tensor y; for tensorLeft it sends x tensor y to (-1)^degree(x) x tensor y. There is no added sign or replacement shift comparison.
* `supportedProductLocalizationSecond` has the identical three-component assertion with `tensorLeft (RΓ_b K)` and the support triangle on Y,d,c,L. Its third component is on X times V and uses restricted L.
* `supportedProductLocalization_naturality` states the square for the specified exterior product under arbitrary morphisms of K and L. It applies at each of the three supports in either triangle, including the restricted coefficient object. The support-comparison isomorphisms are natural transformations or composites of functorial isomorphisms.
* `supportedProductLocalization_openFirst` and `_openSecond` state the canonical supported restriction squares on an arbitrary open of either ambient scheme, again for every support. These apply to each of the triangle components; the actual boundaries are fixed on short exact injective complexes, so the same restriction maps determine their boundary squares. The intrinsic naturality helper theorems have no unnecessary finiteness or boundedness hypotheses; the two principal triangle assertions retain all of the node's hypotheses.
* No exterior-product component is claimed invertible, and no Tor-finiteness hypothesis is introduced.

Dependency declarations read and used:

* `Sheaf.AlgebraicGeometry.SupportCohomology`: `AlgebraicGeometry.Etale.supportSections`, `derivedSupportSections`, and the shared `CategoryTheory.Sheaf.supportedSectionsFunctor` kernel construction. For A-linear supported sections the already landed `Sheaf.AlgebraicGeometry.EtaleSupportedSections` supplies `supportedEtaleSections`, `supportedEtaleSectionsι`, and `derivedSupportedEtaleSections`; no private kernel is defined here.
* `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `AlgebraicGeometry.Etale.derivedTensor`; `Etale.Derived.Kunneth.Defs`: `externalProduct`. Tensor complexes, total tensor, localization comparisons, and monoidal structures all reuse existing APIs.
* `Sheaf.AlgebraicGeometry.DerivedCategories` and the recorded upstream coefficient encoding: `AlgebraicGeometry.Etale.DerivedCategoryModule`, `DerivedCategory.Plus`; Mathlib `DerivedCategory`, `HasDerivedCategory`, and the canonical localization functor Q.
* Mathlib triangulated definitions: `CategoryTheory.Pretriangulated`, `Triangle`, `TriangleMorphism`, `distTriang`, and `Functor.mapTriangle`. In particular, the third morphism equation contains the shifted first component.
* Mathlib schemes, finite type, separatedness and closed immersions: `Scheme`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `IsClosedImmersion`; the recorded `Sheaf.AlgebraicGeometry.BaseChangeConventions` convention is `Limits.pullback`, with `pullback.fst`, `pullback.snd`, and induced `pullback.map`.
* `Sheaf.AlgebraicGeometry.SupportRestrictionTriangle`: the original `AlgebraicGeometry.Etale.supportRestrictionTriangle`, retained by import and refined below by its normalized injective-complex boundary.
* Pullback/direct-image and constant-sheaf adjunction APIs: `upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`, `Scheme.upperStarConstantSheafIso`, and `constantSheafΓAdj`. All derived pullback comparisons use `leftDerivedUpperStarIsoMapDerivedCategory`, `leftDerivedUpperStarComp`, `leftDerivedUpperStarTensorIso`, and `upperStarComp`.
* Mathlib's `DerivedCategory.triangleOfSESδ`, `Functor.rightDerivedFunctorObjQIso`, derived-composition units, `mapDerivedCategoryCompIso`, and exact/derived adjunction transport give the canonical support boundary and comparisons. The postponed existence/uniqueness properties have source and complete proof paragraphs in their owning module. The direct source definition of `externalProduct` is exposed by `supportedExternalProduct_eq` and its equality isomorphism in the comparison module; the underlying construction is unchanged.

Edge cases checked before stating the construction: empty ambient schemes; empty and full supports/cuts; U empty and U all of X (likewise V); zero coefficients and zero derived objects; intersecting or disjoint supports; identity open restrictions; maps equal to identities or zero; complexes with negative nonzero degrees. Kernel restriction handles empty/full opens. All complement identifications are actual equalities of opens rather than equality of nonreduced closed scheme structures. No invertibility of the characteristic, nonzero-ring assumption, regularity, or Tor amplitude is used. The signed tensor comparison is essential for odd first-factor degree in the second-variable boundary.

Sources checked: the item's complete nine-step proof and its source/blueprint metadata; the ancestor `lem-pur-kunneth-supported` proof paragraphs 1 and 3; Stacks [Tag 09XP](https://stacks.math.columbia.edu/tag/09XP) (supported injective restriction triangle), Tag 095L (open-closed coefficient sequence), and [Tag 0F1E](https://stacks.math.columbia.edu/tag/0F1E) (the exterior-product evaluation construction). The node's statement is retained without correction and no statement is disputed.

Searches: the actual msearch outputs are recorded below. Mathlib generic short-exact-complex triangles exist, but no existing supported etale exterior-product localization theorem or the required canonical comparison package was found. Source `rg` searches in WeilConjectures and lean/Sheaf found the existing support kernel and pullback/tensor APIs, not this theorem. DAG and `blueprint_refs.py search` searches for supported coefficient adjunctions and product complements found no owning definition node. The item id has no upstream declaration. The final server-source check found the now-published N4 module `Sheaf.AlgebraicGeometry.SupportedExteriorProduct` and its complete recorded interface on newtargets-dag. Its source and full signatures were read. This delivery imports that module unchanged, including its supported coefficient adjunction, signed complex comparison, normalized derived comparison and supported exterior-product map. The duplicate files and coefficient-adjunction node from the earlier sandbox attempt have been removed; the already-landed exterior-product node is not re-recorded. No files outside this sandbox were edited.

* `leanfinder`: `Supported exterior products commute with localization distinguished triangles and connecting morphisms` → CategoryTheory.Abelian.Ext.preadditiveYoneda_homologySequenceδ_singleTriangle_apply, DerivedCategory.triangleOfSESδ, CochainComplex.homologySequenceδ_quotient_mapTriangle_obj, CategoryTheory.Abelian.Ext.preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply, CochainComplex.homologySequenceδ_quotient_mapTriangle_obj_assoc, CochainComplex.mappingCone.homologySequenceδ_triangleh, CategoryTheory.ShortComplex.ShortExact.singleδ, CategoryTheory.Functor.homologySequenceδ_comp.
* `loogle`: `"supportedExteriorProduct"` → no hits.
* `grep`: `supportedExterior|support.*localization|supported.*[Tt]riangle` → no hits.
* `leansearch`: `Closed supported constant coefficient sheaves left adjoint to sections with support` → service unavailable: Internal Server Error.
* `leanfinder`: `Closed immersion constant coefficient direct image is left adjoint to sections with closed support` → AlgebraicGeometry.Scheme.Modules.instIsLeftAdjointRestrictFunctor, AlgebraicGeometry.Scheme.Modules.restrictAdjunction, AlgebraicGeometry.Scheme.kerAdjunction, AlgebraicGeometry.Scheme.Modules.restrictAdjunction_counit_app_app, AlgebraicGeometry.IsClosedImmersion.overEquivIdealSheafData, AlgebraicGeometry.Scheme.Modules.instIsRightAdjointPushforward, AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app, AlgebraicGeometry.Scheme.kerAdjunction_counit_app.
* `grep`: `supportedCoefficients|supportedCoefficientAdjunction|supportedSections` → no hits.
* `leansearch`: `Canonical identification of support localization triangles after restricting one factor of a product of schemes to an open subset` → service unavailable: Internal Server Error.
* `leanfinder`: `Derived exterior product and sections with support commute with restriction to the product of an open subscheme and another scheme` → ModuleCat.Tilde.toOpen_res, AlgebraicGeometry.exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux_aux, ModuleCat.Tilde.res_apply, AlgebraicGeometry.Γ_map_morphismRestrict, AlgebraicGeometry.Scheme.Hom.appLE_map_assoc, AlgebraicGeometry.Scheme.Hom.appLE_map, AlgebraicGeometry.Proj.fromOfGlobalSections_morphismRestrict, TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst.
* `grep`: `externalProduct.*[Oo]pen|support.*[Pp]roduct.*[Cc]omplement` → no hits.

## New nodes

`def-pur-supported-localization-comparisons`, module
`Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons`, defines the actual open-product
inclusions, the canonical exact/derived-pullback external-product comparison, and the
third-term support transport in both variables. The product-complement isomorphisms are
selected from uniqueness theorems specifying their composites over the original product.
Support changes use equalities of open complements. The external-product comparison
composes the existing monoidal pullback and projection-composition isomorphisms
with the source and target ambient schemes still variables. The open-product
comparison then specializes that construction. This keeps the canonical maps intact
without reopening monoidal proofs at a concrete open subscheme. Its
helper equality theorem exposes exactly the upstream external-product formula; its
isomorphism is `eqToIso` of that equality. Every helper is listed in `lean.declarations`
with a source/blueprint docstring. Searches above found no existing comparison node or
published comparison declaration. The item's stmt_deps gains only this new definition
node. The node binds its coefficient ring explicitly.

## Dependency modules

`lem-pur-support-restriction-triangle` recorded an existential boundary without its
normalization on injective representatives. To state compatibility with the actual
connecting morphisms, `Sheaf.AlgebraicGeometry.NormalizedSupportTriangle` retains the
published theorem by import and adds the normalized interface. Its ordinary arrows are
uniquely determined by their support-kernel inclusions and ordinary restriction. Their
short exact complex on injectives supplies `DerivedCategory.triangleOfSESδ`;
`exists_unique_supportLocalizationBoundary` normalizes the boundary on every termwise
injective K-injective complex using the canonical derived model isomorphisms.
`normalizedSupportTriangle_distinguished` states distinguishedness for exactly the bounded-below inputs of the dependency node. Canonical comparison
units specify the open-composite isomorphisms, and support transport along arbitrary open
immersions is normalized on ordinary sections. The D+ convention is recovered through
`rightDerivedFunctorPlusCompatibility`. Only this dependency node's `lean` field changes.
The closed intersections and supports on opens are actual fibre products. No arbitrary
triangle completion defines a connecting map.

The already-published N4 `supportedExteriorProduct` is used unchanged and its node is not
part of the delivery. Its coefficient and resolution normalization are exactly the ones
needed for the three specified components here.

Validation uses only `scompile.py`, at 60 seconds per file, and `deliver2.py --no-push`.
Every delivered theorem has proof `sorry`; every definition has actual data. The generic
comparison adapters take the upstream `UpperStarPreservesFlat E` interface; their
specializations to `ModuleCat A` use the existing instance for every commutative ring,
so neither principal theorem gains a hypothesis. Derived projection functors are written
exactly as `(upperStar E p).leftDerivedFunctor`, matching the upstream exterior-product
formula and avoiding a redundant wrapper during kernel checking. The comparison module caches the three existing graded-tensor proof instances at a
variable scheme to avoid repeating monoidal sheaf instance search under specialization.
No universe restriction, second tensor product or arbitrary comparison is introduced. Scratchpad files are not
delivered. The independent second reader writes the second-reading section and delivers.

## Second reading by Q06

I independently read the node's statement and nine proof steps, the three delivered Lean
modules, the dependency node statements and their recorded signatures, the published N4
`SupportedExteriorProduct` module, and the earlier `SupportRestrictionTriangle` and
`EtaleSupportedSections` interfaces. I read Stacks `etale-cohomology.tex`,
`section-cohomology-support` (09XP), `remark-define-kunneth-map` (0F1E), and
`lemma-ses-associated-to-open` (095L), from the launcher's literature checkout because
this shared checkout does not contain the TeX files. Section 09XP begins with an arbitrary
scheme, closed subscheme and abelian sheaf; the pairing remark begins with an arbitrary
Cartesian square and ring. Neither silently assumes a characteristic restriction,
properness, regularity or finite Tor amplitude. The finite-type/algebraically-closed
hypotheses of this node are retained from its stated application.

Object/hypothesis/conclusion checklist, written before assessing the implementation:

1. Algebraically closed field k: `k : Type u`, `[Field k]`, `[IsAlgClosed k]` in both
   `supportedProductLocalizationFirst` and `supportedProductLocalizationSecond`. Pass.
2. Finite commutative ring A: `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]` in both
   principal theorems. This is the recorded coefficient convention for the small etale
   module-sheaf categories. It allows finite rings of every characteristic and the zero
   ring after the common universe lift. No field structure on A is assumed. Pass.
3. Schemes over k: `X Y : Scheme.{u}`, and the named structure maps
   `f : X ⟶ Spec (.of k)`, `g : Y ⟶ Spec (.of k)`. Products are `pullback f g`, with
   `pullback.fst` and `pullback.snd` in `externalProduct` and `supportedProductImmersion`.
   These are the recorded base-change conventions, not a Cartesian product over Z. Pass.
4. Finite type and diagonal-separatedness: `[LocallyOfFiniteType f] [QuasiCompact f]`
   and the analogous instances on g, with `[IsSeparated f] [IsSeparated g]`.
   `def-weil-finite-type-morphism` records the first conjunction; the proper-morphism
   node separately records `IsSeparated`. No properness, universal closedness or
   independent Noetherian instance is imposed. Pass.
5. Closed supports B,C in X and D in Y: morphisms b,c,d with their three
   `IsClosedImmersion` instances. `supportIntersection b c` is the fibre-product
   intersection and `supportOnOpen b c.openComplement` is closed base change to U.
   U is exactly `c.openComplement` with inclusion `.ι`. Pass.
6. K and L in D+: the two `DerivedCategory.Plus` binders on
   `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)` and its Y version.
   Their `.obj` fields are used in the unbounded category. F is the published
   `externalProduct ... f g K.obj L.obj`; `_hF : ∃ n : ℤ, F.IsGE n` is precisely its
   required boundedness. The integer bound is existential, not fixed or nonnegative.
   The derived categories and tensor are the dependency declarations. Pass.
7. The first source row is the support-restriction triangle for X,B,C,K tensored on
   the right with `RΓ_D(Y,L)`: `supportedFirstLocalizationSource` applies
   `(tensorRight ((supportedSectionsDerived A d).obj L)).mapTriangle.obj` to
   `normalizedSupportTriangle A b c K`. The first target row is
   `supportedFirstLocalizationTarget`, the normalized support triangle on the actual
   fibre product with support B times D and cut C times Y. The two `distTriang`
   conjuncts state distinguishedness in unbounded `DerivedCategory (ModuleCat A)`.
   Pass; no bounded target category is substituted.
8. Each of the first three displayed products is prescribed individually by
   `m.hom₁ = supportedFirstLocalizationComponent₁ ...`, and similarly for 2 and 3.
   Component 1 uses the published `supportedExteriorProduct` on B intersection C and
   D, followed by `derivedSupportCongruence` from equality of open complements.
   Component 2 is that published product on B and D without modification.
   Component 3 is that product on U times Y with restricted K, followed by
   `supportedFirstLocalizationThirdIso.inv`. Thus the third ambient is genuinely
   U times Y, canonically identified with the open in the product triangle. Pass.
9. A triangle morphism, including the last square: the existential m is a morphism
   in `Triangle`, so its `comm₁`, `comm₂`, `comm₃` include the square involving
   the shifted first component. The boundary is fixed by
   `exists_unique_supportLocalizationBoundary` on every termwise injective
   K-injective representative using `DerivedCategory.triangleOfSESδ` and the
   canonical right-derived model isomorphisms. It is not a chosen completion of
   two commuting squares. Pass.
10. The explicit second-variable assertion: in
    `supportedProductLocalizationSecond`, b is D' in X, d is B' in Y, and c is C'
    in Y. `supportedSecondLocalizationSource` is `tensorLeft (RΓ_b K)` applied to
    the Y,d,c,L row. Its target has product support b times d and cut X times c.
    Components 1,2,3 are the specified products on b with d intersection c, d,
    and d restricted to V, respectively. `supportedSecondLocalizationThirdIso`
    transports the third target through X times V. Pass.
11. The two shift signs: `mapTriangle` uses the global derived-tensor `CommShift`
    instances from `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`.
    I read that construction: it descends the cochain tensor shift comparison and
    identifies the one-variable comparisons on K-flat representatives. The first
    variable has the identity tensor formula; the second has the first-degree sign.
    There is no overriding local instance or an additional sign in either component.
    In odd first degree the second comparison changes sign, as the node requires.
    Pass.
12. Coefficient naturality: `supportedProductLocalization_naturality` states the
    square with arbitrary a:K→K' and e:L→L', the actual bifunctor map on F, and the
    two derived support functor maps. Instantiating at the intersection, full
    support and open product supplies all three component squares. The row arrows
    and boundaries are natural transformations, and the canonical composition and
    tensor comparisons used in the components are functorial. Pass.
13. Open naturality in both ambient schemes: `_openFirst` and `_openSecond` give
    the actual supported restriction square for every support and every open, with
    the canonical product-open coefficient comparison. The original delivery did
    not explicitly state that the row restrictions themselves are triangle
    morphisms, in particular that they commute with the connecting maps. I added
    `supportedProductLocalization_openRows`. It states existence of a triangle
    morphism with all three components fixed to the actual supported restrictions;
    the third component is `supportTriangleRestrictionThird`, defined using
    restriction between the cut complements and the existing exact-pullback
    composition isomorphisms. The hypotheses on restricted supports are just
    equalities of open complements. Together these statements cover the full
    diagrams, including their boundaries, under either ambient restriction. Fixed.
14. No product asserted invertible: neither principal theorem gives `IsIso` for a
    product component. Only geometric/coefficients identifications are isomorphisms.
    No Tor-finiteness is required. Pass.

New node / dependency-module reading:

* `def-pur-supported-localization-comparisons` is absent from the base DAG; its
  construction is the geometric and canonical pullback comparison implicit in
  steps 1,5,8,9, and not a new tensor or new support theory. I checked its fields:
  definition, split, correct chapter/unit, ancestor via this item, explicit A,
  empty proof lists, null Mathlib match, three search kinds, worker creation and
  none-state audits. Both product-complement isomorphisms are chosen from uniqueness
  over the original product, so the choices determine the data up to the equality
  used downstream. The external-product coefficient comparisons are real composites
  of the published exact/derived-pullback, monoidal and projection-composition
  isomorphisms. The intersection comparisons use complements, so do not incorrectly
  identify nonreduced closed subschemes as schemes. I extended this new node's
  statement and module to include the third-term row restriction comparison needed
  by item 13. The cut-complement map uses Mathlib `morphismRestrict`, transported
  along the equality of opens; no arbitrary lift or existence choice is used there.
* `lem-pur-support-restriction-triangle`: I read the original recorded existential
  theorem. It fixes the ordinary arrows and composition units, but leaves the
  boundary as an existential natural transformation with distinguishedness.
  Its lack of the injective short-exact-complex normalization is material here.
  `NormalizedSupportTriangle` retains that theorem by import and supplies this
  normalization, at the same coefficient/site sizes. Its distinguishedness
  theorem takes exactly a D+ object, arbitrary schemes and arbitrary commutative
  coefficients, as the dependency says. The support transport helpers are the
  canonical kernel restrictions and their derived composition comparisons. The
  node changes only in `lean`, with the explanatory note. No repair was needed.
* The already-published N4 `supportedExteriorProduct` was read at its actual source,
  including `supportedSectionsDerived`, the supported coefficient adjunction and
  the signed-complex/localization normalization. Its signature is on exactly the
  categories used here; the principal theorems supply their own finite-type and
  coefficient hypotheses. It is imported, not duplicated or re-recorded.

Edge cases: there is no index set or integer n parameter to restrict; the F lower
bound ranges over all integers, including 0 and negative integers. Empty X or Y,
empty/full B,C,D, empty/full U or V, disjoint supports, nonreduced closed supports,
zero K or L, the zero ring, every characteristic, identity open restriction and
identity/zero coefficient maps are admitted by the binders. Kernel restrictions and
fibre products retain these cases. The new cut restriction uses `morphismRestrict`
even on the empty open. No independent small test-algebra universe can make a
hypothesis vacuous: schemes use u and the recorded module-sheaf convention uses
coefficient/module universe u+1. Generic comparison universes v,w₁,w₂,w₃,w₄ are
explicitly bound; their specialization to `ModuleCat A` introduces no extra instance
assumption in either principal theorem.

Independent searches (in addition to opening the recorded matches):

* LeanFinder, `Tensor cup pairing on local cohomology preserves the connecting
  homomorphism for removal of a closed subset`: eight hits, including adic tensor
  naturality and generic exactness; no etale supported product localization theorem.
* Loogle, `"triangleOfSESδ"`: existing generic short-exact-complex connecting-map
  declarations; these do not state the supported exterior-product theorem.
* LeanSearch, `Canonical restriction morphism of the closed support exact triangle
  along an open immersion`: eight hits, including `morphismRestrict`, `Opens.ι`
  and O-module restriction. I used the existing `morphismRestrict` in the added
  cut-complement adapter; none of the hits gives the required support row theorem.
* LeanFinder, `Pull back a product of closed supports to the open complement in a
  factor and compare derived exterior products`: eight unrelated exterior-algebra
  and profinite hits, no comparison package.
* `rg` on upstream WeilConjectures, Mathlib, shared `lean/Sheaf` and `dag/nodes`,
  using local cohomology, tensor/connecting, localization triangle, cut complements,
  support transport and product-complement terms, found the published supported
  product and the earlier support interfaces. I opened upstream
  `SixFunctors.OpenClosed.Supports`: its triangle is in the derived category of
  sheaves and concerns `s_*s^!I → I → j_*j^*I`; it is not the module-valued,
  arbitrary-B support restriction/exterior pairing assertion here. The algebraic
  `LocalCohomology` modules and `LocalizedTensorComparisonClosureTriangleCore`
  likewise concern different notions. No existing declaration renders this node,
  and no existing DAG node owns the added comparison package.

Mismatch and changes: the sole mathematical omission found was the explicit
open restriction boundary square for the rows (item 13). I added that theorem and
its canonical third-term comparison, extended the new definition node accordingly,
and refreshed the declaration lists and main signature records. The original
principal theorem statements, node statement and proof remain intact; no
`statement_change` or citer audit is required. The sole direct citing node,
`lem-pur-kunneth-supported`, uses exactly the three fixed product components in
its proof steps 2,3,4, and those uses remain valid. I found no hollow definition,
inline sorry data, unbound universe, added characteristic restriction or proved
mathematical theorem. Every postponed theorem has a source/blueprint docstring and
proof plan in its owning node's construction; all theorem proofs remain `sorry`.

Validation: every delivered file compiled cleanly through the prescribed `scompile.py`
wrapper, including the final added comparisons and open-row theorem. The dry run
`deliver2.py Q06 lem-pur-supported-product-localization --no-push` printed OK: all
three final modules compile and the full delivery passes the maintainer's preflight.
The signature/declaration records were also checked against the final Lean text;
all delivered lines are within 100 characters. No warnings were emitted.
