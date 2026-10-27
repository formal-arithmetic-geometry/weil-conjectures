## Worker report

The module `Sheaf.Paper.ClosedTestKInjectiveSectionModels` states
`AlgebraicGeometry.ProEtale.ClosedTestKInjectiveSectionModels.closed_test_kinjective_section_models`.
Its sole postponed proof is that theorem. Every helper has actual construction data;
there are no other postponed theorems. The DAG statement, proof and dependencies are unchanged.

The namespace abbreviations expose the existing module operations and section functors.
`evaluation` is `Mod.forget` followed by abelian-sheaf evaluation, and `complexes` is
`Functor.mapHomologicalComplex (.up ℤ)`. `pushEvaluation` is literally `Iso.refl`:
the internal pushforward forgets to precomposition with geometric base change.
`closedUnit` is evaluation of `CondensedRing.upperStarLowerStarAdjunction.unit`, followed
by restriction along the canonical geometric closed-fibre identification. Thus it uses
the actual module unit, including its coefficient action, rather than an arbitrary map.
`localizationSections` likewise uses the actual module unit, evaluated on the diagonal
of the site object. Its derived version is `Functor.rightDerivedPullback` of this map.
`testArrow` is `pullback.map` for the actual closed-site inclusion and the cartesian square.
`derivedTestPullbackComposition` derives the ordinary coefficient-compatible
`upperStarComp` isomorphisms, with Mathlib's exact-localization factors.
These are helper declarations of the notion stated by this item, not new independent notions.

Hypotheses, individually:

* A commutative condensed ring is the parameter
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `[MonObj Λ]`
  and `[IsCommMonObj Λ]`. This is the unbundled version of `Profinite.CondensedRing`;
  no topological presentation or discrete-coefficient restriction is imposed.
* On each scheme Y, coefficients are exactly `condensedRingObj Λ Y`, the underlying
  ring object of the recorded `coefficientRing Y`. Modules are exactly
  `Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)`.
* The sites are `Scheme.ProEt`, with `Scheme.ProEt.topology`; all schemes and rings
  have universe u, site objects have universe u+1 and morphisms universe u, and section
  groups have universe u+1. This is the existing common sufficiently large universe
  convention; no equality of site object and morphism universes is required.
* The commutative ring A is `(A : Type u) [CommRing A]`; the ideal is `(a : Ideal A)`.
  U and Z are literally `Spec (.of A)` and `Spec (.of (A ⧸ a))`, and `closedMap A a`
  is `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk a))`.
* The affine ind-etale test is `(V : (Spec (.of (A ⧸ a))).AffineProEt)`.
  `liftedTest A a V` is precisely `(closedSiteLift A a).obj V`, included into the full
  pro-etale site by `AffineProEt.toProEt`. `closedTest` includes V by the same functor.
* The two w-contractibility hypotheses are
  `[IsWContractibleRing Γ(V.left, ⊤)]` and
  `[IsWContractibleRing Γ((liftedTest A a V).left, ⊤)]`. They are the recorded ring
  predicate on the global coordinate rings of the two affine schemes.
* The affine morphism is `{X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))`.
  The base-change scheme XZ and its projections are `(h : XZ ⟶ X)` and
  `(fZ : XZ ⟶ Spec (.of (A ⧸ a)))`, with
  `(w : IsPullback h fZ f (closedMap A a))`. Using a specified cartesian square rather
  than Mathlib's chosen representative includes every canonically isomorphic fibre
  product; it is not an additional geometric assumption.
* K is explicitly `DerivedCategory.Plus (...)`. Its image in the ordinary unbounded
  derived category is `K.obj`; no bound on the terms of L or J is imposed.
* The representative is `L : CochainComplex (...) ℤ`, with `[L.IsKInjective]` and
  `e : DerivedCategory.Q.obj L ≅ K.obj`. Mathlib's `IsKInjective` says every map from
  an acyclic complex is homotopic to zero, exactly as in the node.
* The pulled-back resolution is `J : CochainComplex (...) ℤ`, `[J.IsKInjective]`,
  `j : (complexes (CondensedRing.upperStar Λ h)).obj L ⟶ J` and `[QuasiIso j]`.
  `pullRepresentative` is constructed from `Q.map j`, the exact-pullback factors,
  and the supplied e. It makes no additional choice of resolution.

Conclusions, individually:

* The first two conjuncts assert K-injectivity of the actual degreewise pushforwards
  `(complexes (CondensedRing.lowerStar Λ f)).obj L` and the analogous fZ,J complex.
* The next two conjuncts are invertibility of `pushModel` for f,L,e and fZ,J with the
  constructed `pullRepresentative`. `pushModel` is the existing cochain-level universal
  unit `rightDerivedFunctorUnitQ`, followed by the right derived functor applied to
  the representing isomorphism. This says these complexes represent exactly
  `Rf_* K` and `R(fZ)_* h* K`, with their universal-unit normalization.
* `eLeft` has source the derived evaluation at V of exact s-pullback of `Rf_* K`, and
  target `Q(ev_V(s* f_* L))`. Its inverse is explicitly the evaluation-derived unit
  followed by derived evaluation applied to `exactRepresentative` of `pushModel`.
  `exactRepresentative` inserts the inverse of the canonical exact-pullback factor
  before applying exact derived pullback. Thus this is the specified resolution
  comparison, and does not assume `s* f_* L` is K-injective.
* `eUnit` runs from `Q(ev_V(s* f_* L))` to `Q(ev_T L)`. Its inverse is exactly
  `DerivedCategory.Q.map (closedUnitComplex ... (f_* L))`. The source of that complex
  map is definitionally the evaluated f-pushforward at B, namely L(T), by
  `pushEvaluation`. Consequently eUnit is the inverse of the actual closed unit,
  in the direction required by the first displayed line.
* `eRight` has source derived evaluation at V of `R(fZ)_* h* K`, and target
  `Q(ev_V((fZ)_* J))`. Its inverse is the evaluation-derived unit followed by evaluation
  of the specified fZ pushModel. The target is definitionally `Q(ev_T0 J)` by
  `pushEvaluation`, giving the equality in the second displayed line.
* The two `IsIso (localizationModel ...)` conjuncts assert the displayed
  `Q(L(T)) → RΓ(T,K|T)` and `Q(J(T0)) → RΓ(T0,(h* K)|T0)` are isomorphisms.
  These are particular maps, not existential arbitrary isomorphisms. Each map is
  defined as the evaluation-derived unit followed by the canonical derived localization
  map and the actual representing isomorphism. The underlying ordinary localization
  map is evaluation of the unit on the diagonal, which under the slice equivalence
  is the identity `L(T)=(L|T)(id_T)`, including its differentials. This is the source's
  degreewise-identity normalization. Neither test fibre is assumed w-contractible.
* The module's final identification is the explicitly typed construction
  `derivedTestPullbackComposition`, evaluated at K.obj. It identifies restriction
  of h* K to T0 with a-pullback of restriction of K to T, using the closed-site
  inclusion and ordinary pullback composition with its coefficient maps, descended
  termwise. This clause is supplied as an actual definition of the required natural
  isomorphism, rather than a redundant theorem asserting that a chosen isomorphism
  exists and equals itself. Its component at K.obj is the specified map.

Fibre-product convention: Mathlib's site base change uses V ×_U X with projection
`pullback.snd V.hom f`, whereas the node writes X ×_U V. These are the same fibre
product with interchanged ordered factors; the canonical symmetry preserves the
map to X and all section formulas. `testFibre` consistently uses the existing site
base change, avoiding a second site object or a hidden equality transport. The same
convention is used for B, V, XZ, T, T0 and the actual `testArrow`.

Dependency declarations read and used:

* `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`, and their
  commutativity interfaces (reexported through the derived push-pull module).
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and
  `Scheme.ProEt.topology`.
* `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `Mod.forget`.
* `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`.
  The exact inverse image is the recorded `CondensedRing.upperStar`; it is derived
  by `Functor.mapDerivedCategory`. The total direct image is not derived factorwise.
* `WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift`:
  `Scheme.AffineProEt.closedSiteLift`; its geometric inclusion and closed-fibre square
  are in `WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties`,
  `closedSiteLiftInclusion` and `affine_closed_site_functor_properties`.
* `WeilConjectures.RingTheory.ProEtale.WContractible`: `IsWContractibleRing`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.map`, `pullback.lift`, and the projections; `IsPullback` from its API.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`, used
  by the existing closed-site construction. The quotient immersion is constructed
  directly; no extra closed-immersion hypothesis is supplied.
* `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` is publicly
  imported for the recorded general derived-category and right-derived-functor
  declarations. In the present Grothendieck module categories, the existing
  `Functor.rightDerivedFunctor` of moduleObjectDerivedPushforward is its specialization;
  `rightDerivedFunctorUnitQ` in the upstream ShortExactPullback module is the actual
  universal unit with its quotient factors, used throughout rather than redefined.
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` publicly retains
  `ProEtaleTensorComparison.inverseSection`, the recorded ringed-site unit-section
  interface. Here the corresponding internal module unit is used directly; no
  duplicate ringed-site inverseSection is introduced or arbitrary map assumed.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, the recorded slice restriction; the displayed section
  target is its scheme-localization presentation. The ordinary unit on diagonal
  evaluation identifies these presentations with identity on localized sections.

Proof dependencies with statements are imported privately: exact-functor derivation,
ind-etale stability, unbounded section localization, general localized ringed-site
morphisms, exact-derived composition, the right-adjoint K-injective theorem, and the
Mathlib `Localization.liftNatIso` interface for exact-derived natural isomorphisms.
`lem-sfb-closed-test-unit-evaluation` currently has no Lean record and is listed in
this theorem's full proof docstring; no stronger substitute is assumed and no proof
of it is postponed as an untracked helper. The present theorem is only being stated.
The downstream `ClosedTestDerivedExchangeModel` is deliberately not imported, so
there is no proof-import cycle or use of its theorem to define these maps.

Edge cases checked against the actual terms:

* a=0: quotient closedMap and its closed-fibre arrows specialize canonically; no
  proper-ideal hypothesis appears.
* a=⊤: Z and V may be empty; no nonempty hypothesis on schemes, rings, tests, or
  index sets is introduced. The zero-ring case is also permitted.
* X empty, K=0, and zero representative complexes: all evaluations, units and
  pullback maps remain defined; neither nonzero nor positive-degree assumptions occur.
* L and J may be unbounded in both term directions; only K is cohomologically bounded
  below. No degreewise injectivity of the two resolutions is required.
* T and T0 may fail to be w-contractible. The localization assertions use K-injectives,
  not exactness of evaluation on these two objects.
* Different canonical choices of XZ are permitted by `IsPullback`; the supplied
  quasi-isomorphism j and supplied representative e are retained in all normalizations.

Searches for existing statements (2026-10-23):

* msearch LeanFinder, `K injective section models closed pro etale lifted test unit normalized`:
  eight unrelated standard-etale/formally-etale results, no matching statement.
* msearch Loogle, `"IsKInjective", "rightDerivedFunctor"`: no hits.
* msearch grep, `(closed_test|closedTest).*(section|kinjective)`: no Mathlib hits.
* msearch LeanSearch, `Derived sections at a closed proetale lifted test are normalized K injective section complexes`:
  eight generic K-injective declarations, including `CochainComplex.IsKInjective` and
  `CochainComplex.isKInjective_of_injective`; none states this model.
* rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id, `closed_test`,
  `closedTest`, `kinjective.*section`, `closedUnitComplex`,
  `derivedTestPullbackComposition`, and the full theorem name: the existing parent
  exchange theorem concerns the derived mate, not the particular supplied L,J,j
  section models. No exact existing match. Grep of the item id in WeilConjectures
  has no match. `dag/lean_names_upstream.json` was consulted for the K-injective
  and closed-site names. The actual upstream cochain universal-unit helper was
  discovered and reused instead of introducing a duplicate.

Sources read: local Stacks sites-cohomology.tex, lemma-unbounded-cohomology-of-open
(Tag 0D6F) and its K-injective proof; derived.tex, lemma-adjoint-preserve-K-injectives
(Tag 08BJ); proetale.tex, lemma-closed-immersion-affines-apply (Tag 09BL) and proof
of the weakly contractible evaluation description. The current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was read; the item is a proof helper, not that unit's own statement.

No statement correction, dependency module, new node, or disputed statement.

## Second reading by Q119

A separate reread of the node and complete module in this worker turn checked every
hypothesis and clause listed above. This is a self-review; no independent agent was
started, as the dispatch brief explicitly prohibits starting other agents. The
maintainer's independent review remains the independent reading of this delivery.

The reread checked the direction of eUnit carefully: its inverse, rather than its
forward map, equals Q of the actual unit. It checked eLeft and eRight against the
forward universal units and preserved the supplied resolution j in pullRepresentative.
It checked that evaluation-derived comparison for eLeft uses no K-injectivity of
s* f_* L, and that the two localization comparisons do not assume exact evaluation
on T or T0. It checked the geometric orientation of testArrow against the closed
inclusion and the two pullback projections, and checked the explicit type and body of derivedTestPullbackComposition against
the descended ordinary composition. The redundant existential equality for that
constructed isomorphism was removed; the module supplies the isomorphism directly. The only presentation adjustment was to keep
Mathlib's existing ordering V×X of the fibre product consistently rather than create
second site objects with the factors reversed. No mathematical hypothesis or clause
was changed. Generic helper universes are explicitly named, autoImplicit is false,
and every definition has real data.
