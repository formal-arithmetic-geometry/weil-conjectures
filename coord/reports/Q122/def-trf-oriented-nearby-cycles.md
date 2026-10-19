## Worker report

The module `lean/Sheaf/Paper/OrientedNearbyCycles.lean` defines the complete notion in
`def-trf-oriented-nearby-cycles`. Its namespace is
`AlgebraicGeometry.OrientedNearbyCycles`. The main declaration is `nearbyCycles`;
the node's `lean.declarations` lists all 79 constituent declarations. No theorem is
proved: the named construction laws have `sorry` and source/proof-plan docstrings.
Definitions contain actual data or choices specified by universal properties.
There is no statement correction and no STATEMENT-DISPUTED issue.

The clause-by-clause correspondence is:

1. **Arbitrary schemes and coefficients.** Binders are `T B : Scheme.{u}`,
   `f : T ⟶ B`, `Λ : Type v`, `[CommRing Λ]`. Scheme and coefficient universes
   remain independent. `Coeff Λ = ULift.{u+1} Λ` transports the ring by its
   canonical ring equivalence, not a finiteness assumption.
2. **The actual small étale sites and base change.** `EtaleSite X` is Mathlib's
   `X.Etale` transported through `AsSmall.equiv`; `etaleTopology` is its induced
   topology. Thus objects, arrows and coverings are those of the recorded
   `Scheme.smallEtaleTopology`, up to equivalence. `etaleBaseChange f` is
   `AsSmall.down ⋙ MorphismProperty.Over.pullback @Etale ⊤ f ⋙ AsSmall.up`.
   Its value is the actual scheme fibre product. This raises the morphism
   universe rather than imposing equality between the original site universes.
3. **Concrete vanishing site and topos.** `VanishingSite f` is the recorded
   `OrientedProduct.Triples (etaleBaseChange f) (𝟭 _)`, not an unspecified topos.
   `vanishingTopology f` uses exactly `OrientedProduct.topology` with the two
   transported étale pretopologies, hence the three specified covering types.
   `VanishingTopos f` is the actual category of set-valued sheaves on that site.
4. **Projections.** `first`, `second` reuse the recorded triple-site functors;
   `p₁`, `p₂` use their actual sheaf pullback/pushforward adjunctions via
   `siteMorphism`. `projection_properties` records continuity and finite-limit
   preservation; it adds no hypothesis to the definition.
5. **Orientation and universal property.** `orientation_existsUnique` specifies
   every component of the direct-image transformation by ILO XI 1.3: restriction
   to the middle triple, followed by inverse restriction along the type-(c)
   cover. `map_toFirst_isIso` is ILO XI 1.2(ii). The predicate also includes the
   recorded `OrientedProduct.IsUniversal`. Thus `orientation` has precisely
   direction `p₂ ⇒ f p₁` on direct images, with the reverse inverse-image mate.
   `orientation_universal` and `lift` retain both projection identifications and
   the orientation compatibility, rather than choosing an arbitrary map.
6. **The nearby-cycle geometric morphism.** `psiLift f` applies that universal
   property to `(identity _, etaleMorphism f, identity)` (the identity is written
   with the canonical functor unitors). `psi f` is its geometric morphism.
7. **Constant ring and module categories.** `etaleDatum` and `vanishingDatum`
   reuse `AdicSites.Site`. `Site.ring` is the existing `constantSheaf` of the
   coefficient ring; `Site.modules` is the recorded actual `ringedSiteModules`
   (`SheafOfModules`), never a new abstract category.
8. **Unbounded derived category.** `EtaleDerived` and `VanishingDerived` use
   `Site.derived`, namely Mathlib's unbounded `DerivedCategory` with its standard
   localization instance. No boundedness or constructibility binder is added.
9. **Module and derived inverse/direct images.** `moduleMorphism` transports
   the ring and module operations using the existing `InverseImageData`, with
   its natural constant-ring identification. `Morphism.modulePull` is the
   actual algebraic inverse image followed by scalar extension along that
   identification. Its exactness is the existing `modulePull_properties`.
   `Morphism.pull` applies it termwise and localizes. The direct image is its
   representing module right adjoint, with the fixed `moduleAdjunction`.
   `Morphism.push` is the existing K-injective total right derived functor;
   `Morphism.adj` is the induced derived adjunction. These are the existing
   constant-coefficient specialization of the repaired general adjunction
   dependency, not extra data assumed from the user.
10. **RΨ.** `nearbyCycles f Λ := (psiModules f).push (Coeff Λ)` is therefore
    `R ψ_f,*`, on the entire unbounded category. K-injective resolutions are
    supplied by the existing `Site.hasKInjectives` instance. There is no new
    choice of an arbitrary derived functor or counit.
11. **Dᵇ.** `IsBounded` abbreviates the existing standard derived
    t-structure's `bounded` predicate; `BoundedDerived` is exactly Mathlib's
    `DerivedCategory.Bounded (S.modules A)`. `isBounded_iff` explicitly states
    its characterization `∃ a b : ℤ, ∀ n, n < a ∨ b < n → IsZero
    ((DerivedCategory.homologyFunctor _ n).obj L)`, with its proof postponed.
12. **An arbitrary commutative square.** `squareDirect` uses actual fibre-product
    composition and the equation `comm : h ≫ f = f' ≫ g`.
    `squareOrientation` is the whiskered orientation through this equation.
    `squareLift` applies the recorded universal property to `h p₁'`, `g p₂'`.
    `squareMorphism` is the induced `v`, with no Cartesian hypothesis.
13. **The specified square at ψ.** `squarePsiFirst`, `squarePsiSecond`,
    `psiHFirst`, `psiHSecond` give the identifying maps on both projections.
    `squarePsi_existsUnique` fixes the isomorphism by those two equations, and
    `squarePsi` selects it. Thus the isomorphism is projection-compatible.
14. **Its module/derived comparison.** `moduleSquare_existsUnique` specifies
    the map on *every* scalar-extension insertion, using the actual set-sheaf
    square. Linearity and sheafification force uniqueness. `derivedSquare`
    applies the existing termwise exact-functor localization maps.
    `nearbySquare` uses the inverse mate of `squarePsi`, in the direction
    `v^* ⋙ ψ_f'^* ≅ ψ_f^* ⋙ h^*`. This is not an arbitrary natural isomorphism.
15. **Ordinary comparison β.** `baseChange` is literally
    `((psiModules f').adj _).homEquiv _ _` applied to `nearbySquare.hom`
    followed by `h^*` of the *same fixed* adjunction counit at `L`.
    Its endpoints are exactly `v^* RΨ_f L` and `RΨ_f' h^* L`.
16. **Ψ-goodness.** `IsPsiGood` universally quantifies over
    `B' : Scheme.{u}` and every `g : B' ⟶ B`; it uses the actual categorical
    pullback, `pullback.fst`, `pullback.snd`, and `pullback.condition` to require
    `IsIso (baseChange ...)`. All test schemes in the chosen scheme universe
    are covered; there is no independent smaller test universe, nor a
    Noetherian, proper, surjectivity, finite-type or coefficient restriction.
17. **Derived tensor.** `derivedTensor` abbreviates the existing
    `SheafOfModules.wfSiteDerivedTensor`, itself selected from the recorded
    `wf_site_derived_tensor_descent`. `flatRepresentatives` is precisely
    K-flat complexes with flat terms. `tensorModel_exists` retains the natural
    representative comparison and the unique compatible isomorphism with
    every other representative model. No second derived tensor is introduced.
18. **Tensor-preserving pullback.** `tensorEdge` builds the already defined
    `RingedTensorEdge` from these actual module functors. Its ordinary tensor
    comparison uses `canonicalRingedTensorComparison_existsUnique` (existence
    *and subsingleton*), with the generalized pure-tensor normalization.
    `pullTensor` is the existing canonical derived comparison on the chosen
    K-flat models. Its direction is `u^*(P ⊗ᴸ Q) ≅ u^*P ⊗ᴸ u^*Q`.
19. **Lax tensor μ.** `laxTensor` is literally the adjunction transpose of
    `pullTensor.hom` followed by `derivedTensor.map (Prod.mkHom ε_L ε_M)`.
    Both counits are from the same `psiModules.adj` as in β.
20. **External products.** `productMap f₁ f₂` uses the actual fibre product and
    its first projection. `product_first_comm`, `product_second_comm` express
    its two projection squares; `productFirst`, `productSecond` are the
    corresponding `squareModules`. `externalEtale` is tensor of the two exact
    derived étale pullbacks; `externalVanishing` is tensor of the two induced
    derived vanishing-topos pullbacks. Their domains are the stipulated actual
    derived categories, and their codomains use this same fibre product.
21. **Künneth comparison.** `kunneth` is the literal composite
    `derivedTensor.map (Prod.mkHom (baseChange ... L₁) (baseChange ... L₂)) ≫
    laxTensor ...`. Its target is `nearbyCycles` of `externalEtale`; the source
    is `externalVanishing` of the two nearby-cycle objects. The module makes
    no invertibility assertion about this map.

Sources read: the local ILO PDF, Exposé XI 1.1--1.7, 1.9 and 4.1--4.3
(the sandbox text extract is only scratch material). I also located and read
Illusie's §§1.4--1.5 and 2.1 in the author's PDF:
https://www.imo.universite-paris-saclay.fr/~luc.illusie/Illusie-nearby-cycles28.pdf .
In particular, 1.5 defines goodness by arbitrary Cartesian base change and 2.1
constructs Künneth as the tensor of base-change maps followed by the lax tensor
map. The node's extension to unbounded categories is explicitly requested by
its statement and supported by its K-injective dependencies; no boundedness
restriction from the source's earlier notation was silently imposed.

Dependency declarations used (including the canonical helpers reused from
published modules) are:

- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`,
  `Scheme.smallEtaleTopology`; `MorphismProperty.Over.pullback` and
  `pullbackComp` supply actual étale base change.
- `Sheaf.CategoryTheory.Sites.OrientedProductUniversal`:
  `OrientedProduct.Triples`, `topology`, `first`, `second`, `middle`,
  `toFirst`, `toSecond`, `paste`, `IsUniversal`, and the universal-property
  theorem underlying the specialization.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`: `GeometricMorphism`,
  `comp`, `inverseIso`; the existing unringed geometric-morphism definition.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`;
  its homology functor defines the finite cohomological interval.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `Sheaf.Paper.ConstantCompletionEquivalence`: `constant`, `Mod`, `D`,
  `InverseImageData`, `inverseImageData_exists`, `pull`, `constantMap`,
  `pullInsertion`, `underlying` and `insertion`; these helpers do not require
  the Noetherian/completion assumptions of that module's main theorem.
- `Sheaf.Paper.CompletionMateComparison`: `AdicSites.Site`, `Site.ring`,
  `Site.modules`, `Site.derived`, `Site.hasKInjectives`, `AdicSites.Morphism`,
  `Morphism.modulePull`, `modulePull_properties`, `modulePush`,
  `moduleAdjunction`, `pull`, `push`, `adj`; these generic helpers likewise
  have no completion or Noetherian hypothesis.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`:
  `SheafOfModules.module_pullback_pushforward_adjunction`, the general
  tensor-formula module-adjunction dependency repaired below.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` and the
  imported K-injective APIs: the prescribed K-injective total derivation;
  `CochainComplex.IsKInjective` is the Mathlib notion, not a new predicate.
  `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses` supplies
  the recorded general module-sheaf resolution existence theorem.
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors` and
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`:
  the general derived-adjunction interface and the exact/K-injective
  specialization used by `Morphism.adj`.
- `Sheaf.Algebra.Homology.KFlat`: the existing `CochainComplex.IsKFlat` and
  its independent-coefficient formulation. `SheafOfModules.IsFlat` is the
  recorded tensor-exact flatness predicate.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality` and the
  imported tensor modules: actual sheafified module tensor and scalar change.
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`:
  `SheafOfModules.wf_site_derived_tensor_descent`;
  `Sheaf.Paper.WeilTensorProduct`: `SheafOfModules.wfSiteDerivedTensor`.
- `Sheaf.Paper.RingedTensorSquarePresentation`: `RingedTensorCorner`,
  `RingedTensorModel`, `RingedTensorEdge`, `RingedTensorEdge.tensorComparison`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`:
  `canonicalRingedTensorComparison_existsUnique` and its normalized derived
  comparison, the common-universe specialization of the recorded
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` interface.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryCompIso`, `mapDerivedCategoryNatIso`.

The five added `stmt_deps` are already landed definition/interface owners of
these exact reused helpers. A read-only traversal found no path from any of
those nodes back to this item. There are no new independent notions or nodes.

Edge cases checked against types and constructions: `T = ∅`, `B = ∅` whenever
`f` exists, the zero coefficient ring, zero complexes, `f = id`, identity
squares, and arbitrary non-Cartesian commutative squares. The site/topos
constructions retain empty objects and their coverings. None of the signatures
requires inhabited schemes, a nontrivial ring, boundedness or finite type. The
empty cohomological interval is allowed and contains zero objects. For the
identity square, the insertion-normalized comparison and the triangle identity
recover the identity base-change arrow; no assertion that `V_id` is the étale
topos is made. For arbitrary squares β is defined, while goodness only tests
the actual Cartesian base-change squares. The product construction also allows
empty fibre products and has correctly directed `v_i^*`.

Searches made for the item:

- `msearch.py ... leanfinder "Oriented nearby cycles on the vanishing topos
  with Psi-good base change and Kunneth comparison"`: 8 unrelated results
  (restriction cycles/local cohomology and related declarations); no match.
- `msearch.py ... loogle "nearbyCycles, OrientedProduct, GeometricMorphism"`:
  no match; `nearbyCycles` is unknown.
- `msearch.py ... grep "nearby.?cycle|vanishing.?topos|oriented.?prod|Psi.?good"`:
  no Mathlib hits.
- `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, including the
  item id and nearby-cycle/oriented-product names: no existing definition.
- `rg` over the shared `lean/Sheaf`: the oriented-product universal module is
  present and is reused; no nearby-cycle/goodness/Künneth definition exists.
- A follow-up Mathlib search found `DerivedCategory.Bounded` and the standard
  `TStructure.t.bounded` predicate. These are reused directly for Dᵇ; the
  finite-cohomological-interval clause is an explicit characterization theorem.
- Follow-up API searches found and reused the constant-module exact pullback,
  K-injective direct image, localized K-flat tensor and normalized tensor-edge
  interfaces listed above, rather than duplicating these notions.

Compilation: the prescribed `scompile.py Q122 def-trf-oriented-nearby-cycles`
compiled the complete module both in its sandbox and under its library module
name, with no error or warning. The final delivery dry run below repeats the
required per-file checks. No global build or direct repository mutation was run.

## Dependency modules

`lem-weil-pbc-ringed-topoi-module-adjunction` receives a lean-only §1(B) repair
with `existing: true`. The former record names
`AlgebraicGeometry.ProEtale.ringedTopoiModuleAdjunction`, restricted to scheme
pro-étale morphisms and a monoid coefficient object. The geometric morphisms
introduced by the oriented-product universal property are not supplied as
scheme pro-étale maps. The already published
`SheafOfModules.module_pullback_pushforward_adjunction` in
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction` instead states the
node for arbitrary small sites, arbitrary commutative ring sheaves, and the
specified geometric adjunction. It identifies the transported inverse ring,
module inverse image, direct image and actions, scalar-extension functor and
its hom-equivalence with the given set adjunction, normalized by `m ↦ 1 ⊗ m`.
The signature was read in full. Its common universe is met by the explicit
site transport above, with neither scheme nor coefficient universe restricted.
Every other field of this dependency node remains verbatim unchanged; no new
module or mathematical statement is needed for this exact existing match.

Independent mathematical review is assigned to the maintainer by this worker
brief. No second agent was started and no independent-review claim is made here.

## Second reading by Q122

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
