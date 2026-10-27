## Worker report

`Sheaf.AlgebraicGeometry.ProperOpenAlphaPasting` states the three clauses as
`AlgebraicGeometry.ProEtale.StrictTower.alpha_vertical_beforeDerivation`,
`alpha_horizontal_beforeDerivation`, and `alpha_baseChange_beforeDerivation`.
Every theorem proof is `sorry`; every definition has actual data. The item's statement is unchanged mathematically and now cites the separate ordinary-arrow definition node alongside the published derived-arrow node. The item proof and all theorem clauses remain unchanged. The returned duplicate is removed. The ordinary module imports existing open-unit, clopen-projector, cartesian-beta and open-compositor declarations; its new definition node owns only the missing ordinary alpha interface.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- An arbitrary commutative coefficient ring is `(B : Type (u + 1)) [CommRing B]`.
  There is no finite, torsion, nonzero or characteristic assumption. All schemes
  are `Scheme.{u}`. These are the universes of the recorded framework: the small
  pro-etale site's objects live in u+1 and morphisms in u. No equality of those
  site universes is imposed.
- The recorded `coefficients B X` is `(constantSheaf (Scheme.ProEt.topology X)
  CommRingCat.{u+1}).obj (CommRingCat.of B)`; `Modules B X` is its module-sheaf
  category; `Towers B X` is `ℕᵒᵖ ⥤ Modules B X`, with n representing positive
  level n+1. `Derived B X` is the ordinary unbounded derived category of this
  strict-tower category. These notions are all used unchanged.
- Ordinary inverse image and open extension are the recorded `modulePullback`
  and `moduleJ`. Derived inverse image, direct image and open extension remain
  `G`, `R` and `J`, with the original `adj` and `jAdj`. No direct-image exchange
  is substituted for an inverse-image square identification.
- Each square has exactly k:V→W, i:S→T, r:V→S, p:W→T,
  `[IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]`,
  `[IsProper r] [IsProper p]` and `h : k ≫ p = r ≫ i`. Thus the original square
  need not be cartesian. The ordinary `singleAlpha` is beta for `pullback p i`,
  followed by `clopenModulePi` for the existing `squareLift k r p i h`, and precisely
  the inverse-image and open-extension compositors. The published `alpha` is
  the same intrinsic construction on derived towers. Neither is a variable or
  an arbitrary comparison satisfying a desired law.
- Vertical pasting: k,i,j are the top, middle and bottom quasi-compact opens;
  r₁,r₂,p₁,p₂ are proper. h₁,h₂ are the two square commutations. The outer
  equality proof h is forced by these commutations and associativity, so its
  explicit binder adds no mathematical assumption. `alphaVerticalPasted`
  first inserts `moduleGComp B p₁ p₂`, then applies the second alpha under
  p₁ inverse image, then the first alpha on r₂ inverse image. Its equality
  with `alphaVerticalOuter` identifies this with the intrinsic outer alpha
  followed by `moduleGComp B r₁ r₂`. The final conjunct states the same
  equality at every `N : Derived B E`, using the specified `gComp` and `alpha`.
- Horizontal pasting: k,l are the top opens, i,j the bottom opens; all four
  are open and quasi-compact, and r,p,q are proper. h₁,h₂ and their forced
  outer equation h express the commutations. `alphaHorizontalOuter` inserts
  `openBetaModuleJComp B i j` before intrinsic outer alpha. `alphaHorizontalPasted`
  applies alpha₂ on i-extension, then l-extension of alpha₁, and finally
  `openBetaModuleJComp B k l`. Their equality is exactly the horizontal formula.
  The last conjunct uses the corresponding existing derived `jComp` formula.
- Arbitrary base change: b:T₁→T is the node's h, and a,c,d are its W,S,V
  projections. wk,wi,wp,wr are the four face commutations. sk,si,sp,sr are
  `IsPullback` on the four lateral faces. This is the invariant presentation
  of the induced cube, allowing arbitrary representatives of its fibre
  products. It adds no cartesianness assumption on Q or Q₁ and no condition
  on b. The open, quasi-compact and proper instances on changed arrows are
  exactly their base-change properties. sp and sr preserve the induced-cube
  hypothesis even though this equality only needs the other cartesian faces.
- `alphaCubeOriginal` starts with `moduleSquareG B a p₁ p b wp` (theta), then
  inverse image of alpha_Q along a, beta_k, and the inverse square comparison
  for wr. `alphaCubeChanged` applies inverse image along p₁ of beta_i, then
  alpha_Q₁ on c-inverse image. Their equality is the cube formula. The final
  conjunct repeats exactly this formula with `squareG`, `beta`, and `alpha`.
  Functor-composition notation gives theta as `G_b ⋙ G_p₁ ≅ G_p ⋙ G_a`, the
  same orientation as the node's operator-composition notation.
- In each theorem there are five conjuncts: the actual module-sheaf equality;
  its degreewise image on arbitrary complexes of module sheaves; its actual
  termwise image under `Functor.whiskeringRight ℕᵒᵖ`; its degreewise image on
  unbounded complexes of strict towers; and the equality on every derived
  strict-tower object. Naturality includes tower transitions and differentials.
  No derived evaluation-faithfulness premise appears. Natural transformations
  are equal exactly when all their components are equal, so the last conjunct
  is the desired transformation equality.
- The owning definition node includes `alpha_eq_localized_singleAlpha`:
  it uses the existing `ClopenProjectorDescent` predicate to state the
  localization representative equation between the actual termwise ordinary
  alpha and the specified intrinsic derived alpha. The predicate equates
  delta on Q(K), followed by the target factorization, with the source
  factorization followed by Q of the ordinary chain map, for every complex K.
  Localization uniqueness makes this equivalent to equality with exact descent.
  Both exact-derived composition isomorphisms are inserted, with the existing
  `clopenTowerAbelian` and `towers_hasDerivedCategory` instances explicit. Thus the equations before
  and after derivation concern the same construction. Each route definition
  explicitly inserts all associators and the specified compositors.

Dependency modules and declarations read:

- Mathlib.AlgebraicGeometry.Scheme: Scheme and Scheme.Hom;
  Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and ProEt.topology;
  Mathlib.CategoryTheory.Sites.ConstantSheaf: constantSheaf.
- Sheaf.CategoryTheory.RingedSiteModules: ringedSiteModules, transparently
  Mathlib's SheafOfModules. The strict framework uses this same category.
- Mathlib.CategoryTheory.Functor.OfSequence: Functor.ofOpSequence and
  NatTrans.ofOpSequence, with the n↔n+1 indexing convention;
  Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory and
  HasDerivedCategory, with the framework's standard instance.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback,
  pullback.fst, pullback.snd, pullback.lift and their projection equations;
  Mathlib.AlgebraicGeometry.OpenImmersion: IsOpenImmersion;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact;
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.Proper: IsProper;
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion.
- Sheaf.AlgebraicGeometry.StrictConstantTowerOperations: coefficients, Modules,
  Towers, Derived, modulePullback, moduleDirectImage, moduleGComp, G, R, gComp
  and their exactness and adjunction interfaces.
- Sheaf.AlgebraicGeometry.StrictTowerOpenExtension: moduleJ, moduleJAdj,
  towerJ, J, jAdj, jComp, jCongr. The ordinary `openBetaModuleJComp` is the
  unit-preserving left-adjoint conjugate of the recorded `moduleGComp`.
- Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized: moduleSquareG and
  singleBetaInv. Despite the filename, those declarations have arbitrary B;
  only the later invertibility theorem in that file assumes `[Finite B]`.
- Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows: squareLift with its
  clopen instances; squareG, beta, pi, alpha, gamma, exchange. The repair
  publicly imports this module, retaining its entire interface.
- Sheaf.AlgebraicGeometry.OpenImmersionSquare: OpenImmersionSquare and its
  ChosenCartesianSquare parent. IsPullback expresses the same invariant
  cartesian property required by the recorded beta interface.
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations:
  Scheme.proEtaleRingModuleAdjunction. This is the actual specified
  constant-section-normalized adjunction; no new adjunction is chosen.
- Sheaf.AlgebraicGeometry.ProperOpenClopenProjector:
  clopenModule_openUnit_isIso, clopenModuleToDirect,
  clopenModuleToDirect_isIso, clopenModulePi, ClopenProjectorDescent and
  clopenTowerAbelian. The ordinary alpha uses exactly clopenModulePi.
- Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization: openBetaModule,
  openBetaModule_isIso and openBetaModuleJComp. Their full signatures have
  arbitrary B and exactly the cartesian/open hypotheses used here.
- Proof-only imports: Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed,
  Scheme.proEtale_ringed_open_closed; and
  Sheaf.CategoryTheory.ExactDerivedTransformationPasting,
  ExactDerivedPasting.exact_derived_transformation_pasting.
  The previously missing normalization and clopen-projector nodes are now
  recorded on the live base; their public modules are used as statement
  dependencies of the ordinary-arrow definition node.

Sources: the statements and proofs in local Stacks more-etale.tex labelled
lemma-shriek-proper-and-open-compose, -compose-horizontal and -base-change
(Tags 0F7C, 0F7D, 0F7F), and the open localization/open-closed ingredients of
proetale.tex (09AH, 09BN). The arbitrary-B underived refinement is explicitly
agent-written in the DAG; Stacks states the proper/direct-image mate version.
The delivered proof docstrings carry all seven node steps: module-sheaf
restriction detection, beta normalization, normalization of intrinsic alpha,
the relevant restriction calculation, and termwise/degreewise exact descent.

Edge cases checked: the zero ring and infinite rings; empty opens and empty V;
identity opens and verticals; cartesian Q (its lift is canonically identity and
alpha reduces to beta); noncartesian Q with an extra component in W×_T S
(the actual pi discards it); identity, empty and arbitrary nonproper base
changes; and complexes unbounded in both directions. None is excluded.

Searches through msearch.py, recorded in searches.jsonl:

- leanfinder, "Clopen proper open alpha natural transformations obey vertical
  horizontal pasting and arbitrary pullback on proetale module sheaves and
  strict towers": 8 hits, scheme-module pseudofunctor associativity and sheaf
  presentations; no match for intrinsic alpha before derivation.
- leansearch, "Clopen proper open alpha comparison on proetale sheaves commutes
  with vertical horizontal square pasting and arbitrary pullback": 8 hits on
  gluing, pullback pasting and sheafification; no exact match.
- loogle, "CategoryTheory.whiskerLeft, CategoryTheory.whiskerRight": invalid,
  unknown CategoryTheory.whiskerLeft. Corrected query
  "CategoryTheory.NatTrans, CategoryTheory.Adjunction": 0 hits.
- grep, "properOpen|proper_open|clopen.*pasting|alpha_vertical": 0 Mathlib hits.
- Direct rg of WeilConjectures and Sheaf found StrictTower.alpha_vertical,
  alpha_horizontal, alpha_baseChange in StrictTowerProperOpenCalculus. Their
  full signatures give only the derived equalities, omitting this item's
  before-derivation assertions. They belong to the downstream calculus and
  are not imported as a circular proof dependency. Direct item-id search in
  WeilConjectures found no existing declaration. Varying-ring system versions
  have a different underlying category; their definitions are not copied.
- For the new ordinary-arrow node, msearch LeanSearch and LeanFinder queries for
  canonical clopen projectors and ordinary alpha returned only generic clopen,
  sheaf and pullback facts; grep of Mathlib, `WeilConjectures/`, `lean/Sheaf/`,
  and `dag/nodes` found no `singleAlpha`, `clopenModulePi`, `singleOpenToR`, or
  `openBetaModule` owner. `tools/blueprint_refs.py search ordinary proper
  open` returned zero blueprint nodes. The existing derived interface therefore
  remains the dependency and the ordinary constructions have their own node.

## New nodes

`def-cbc-strict-tower-ordinary-proper-open-arrows` owns `singleJCongr`,
`singleAlpha`, `towerAlpha`, and `alpha_eq_localized_singleAlpha` in
`Sheaf.AlgebraicGeometry.StrictTowerOrdinaryProperOpenArrows`. It introduces
arbitrary constant coefficients and the existing ordinary module/tower functors;
uses the existing cartesian beta, normalized open compositor, open unit,
direct-image transpose and clopen projector; defines equality transport and the
intrinsic alpha; extends alpha termwise; and states that exact localization is
the already specified derived alpha. Its source is the ordinary strict-tower
refinement of Stacks 0F7B--0F7F and 09BN. The earlier three-kind searches are
retained as historical results; the repair search records which ordinary
notions are now supplied by existing modules. The existing clopen-projector
and beta-normalization nodes are cited, and no notion they own is redeclared.
The single remaining postponed localization theorem has the matching clause
in the new node and its full proof plan in the docstring. All definitions have
real data; the module's only theorem proof is `sorry`.

## Dependency modules

The returned dependency record `def-cbc-strict-tower-proper-open-arrows` is restored byte-identically from the live repository. Its module is `Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows`, with declaration `AlgebraicGeometry.ProEtale.StrictTower.gamma` and its original 18-declaration interface. The ordinary module publicly imports this module and adds the missing ordinary alpha interface; it does not overwrite or duplicate the published declarations. The item's `stmt_deps` contains both node IDs, and its TeX statement cites both at the intrinsic-alpha clause.

The other recorded dependencies and declarations are unchanged: Mathlib.AlgebraicGeometry.Scheme, Mathlib.AlgebraicGeometry.Sites.Proetale, Mathlib.CategoryTheory.Sites.ConstantSheaf, the strict constant-tower operations, strict tower open extension, finite-open base-change normalization, and OpenImmersionSquare. Their full signatures were read before writing the ordinary interfaces. No dependency record is changed by this repair. The existing clopen-projector and beta-normalization records are used unchanged.

## Second reading by Q95

I opened both final Lean modules, the item node, the new definition node and the
recorded clopen-projector/beta-normalization interfaces. This is a self-check;
the dispatch forbids starting other agents, and the maintainer supplies the
independent review. The hypothesis/clause correspondence above still holds:
arbitrary B; the exact recorded module, tower and derived categories; all
proper and quasi-compact-open hypotheses; both pasting laws; an arbitrary
induced pullback cube; and all five equalities for each law. Empty opens, zero
rings, identity maps, noncartesian original squares and unbounded complexes
remain admitted. The ordinary paths use the existing canonical openBetaModule,
openBetaModuleJComp and clopenModulePi, so replacing the duplicates changes no
mathematical map. The localization clause uses the existing representative
equation predicate and explicit existing abelian structures, without a new
instance or a size restriction. Both modules keep autoImplicit false and
contain no file-local notion or instance.

The current clopen-projector and normalization nodes have no dependency path
back to this item (both statement and proof dependencies checked), so adding
them to the new ordinary definition node creates no DAG dependency cycle.
The item module's recorded signature is unchanged, and its three theorem
proofs remain sorry. The published derived-arrow node is still untouched.

## Returned duplicate repaired

Return L at immutable head 93ca8644a20f identified singleOpenUnit_isIso as a
restatement of FiniteOpenBaseChangeNormalized.openUnit_isIso. I removed the
declaration and its ownership record. Reading that existing source with
scompile.py --source shows the complete binders are
`(B : Type (u + 1)) [CommRing B] [Finite B] [TopologicalSpace B]
[DiscreteTopology B] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]`.
It is private, so it is not a usable arbitrary-ring public theorem. The current
public `clopenModule_openUnit_isIso` has exactly
`(B : Type (u + 1)) [CommRing B] {U X : Scheme.{u}} (j : U ⟶ X)
[IsOpenImmersion j] : IsIso (moduleJAdj B j).unit`, matching the needed claim
with no finite or topology binder. I use that interface through its existing
`clopenModulePi`, which is defined from `clopenModuleToDirect`, itself defined
using that theorem. The corresponding duplicate transpose, invertibility
statement and projector were removed as well.

The current beta-normalization module also supplies the exact ordinary beta
and open compositor. I removed singleBetaInv_isIso_arbitrary,
singleBetaArbitrary and singleJComp and changed every consumer to
openBetaModule or openBetaModuleJComp. The new node cites both existing owners.
These changes retain the saved packet's alpha statements and repair its
ordinary dependency interface against the current published sources.

Validation: the initial retained packet passed deliver2.py --no-push. After
the actual repair, scompile.py compiled each of the two final modules
separately in dependency order with no errors or warnings. The imported
module exposed a universe-inference ambiguity in the old raw localization
expression; using its existing ClopenProjectorDescent predicate with explicit
clopenTowerAbelian instances resolved it without changing the claim.

## Statement corrected

The item’s mathematical statement is unchanged. The serialized TeX sentence now cites `def-cbc-strict-tower-ordinary-proper-open-arrows` alongside the restored published arrow node because the ordinary `singleAlpha` construction was moved to that new owner. The required `statement_change` records this citation-only repair. The only citer is `lem-cbc-strict-tower-proper-open-calculus`; it names the item only in `proof_deps`, so its use remains valid (`holds: true`).
