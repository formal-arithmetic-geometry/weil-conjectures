## Worker report

The module `Sheaf.Paper.LocalizeRingedSiteMorphism` states
`SheafOfModules.localize_ringed_site_morphism`, with `sorry` as its entire proof.
No definitions, auxiliary theorems, new nodes, or dependency replacements are added.
The node is unchanged except for its Lean record.

Hypothesis and conclusion correspondence:

- Small sites C,D: `{D C : Type u} [SmallCategory D] [SmallCategory C]`,
  precoverages `K,J`, and the four site-axiom instances for each. Their associated
  Grothendieck topologies are `K.toGrothendieck` and `J.toGrothendieck`.
  The single ambient universe contains the sites, coefficient rings and module values;
  it is arbitrary, and imposes no cardinality bound independent of that ambient universe.
- Continuous u defining f: `u : D ⥤ C`, `hcover` is preservation of covering families,
  `hpullback` is preservation of pullbacks along covering arrows. The `IsContinuous`
  instance is the sheaf-preservation consequence, as in the sites dependency record.
  `Functor.sheafPushforwardContinuous` is precomposition and its left adjoint is
  `Functor.sheafPullback`. Finite-limit preservation of this left adjoint on sets
  is the displayed `PreservesFiniteLimits` hypothesis. Existence of the adjoints
  is inferred for these small sites, never added as an extra assumption.
- R,S commutative ring sheaves and c: `R : Sheaf K.toGrothendieck CommRingCat`,
  `S : Sheaf J.toGrothendieck CommRingCat`, and
  `c : (u.sheafPullback CommRingCat ...).obj R ⟶ S`.
  This is the inverse image on ring sheaves, whose adjunction is the algebraic
  lift of the set-sheaf adjunction of the geometric morphism. Its adjunct is written
  explicitly as `(u.sheafAdjunctionContinuous CommRingCat ...).homEquiv R S c`.
- V and U=u(V): `(V : D)` and the literal `u.obj V` throughout.
- Localized sites and coefficients: `Over V`, `Over (u.obj V)`, topology `.over`,
  coefficient sheaves `R.over V`, `S.over (u.obj V)`, and the existing module
  `overFunctor`. No copied topology, restriction or module category is introduced.
- The localized functor is exactly `Over.post (X := V) u`. The first two conjuncts
  state its preservation of coverings and the required pullbacks, using
  `Presieve.overEquiv` to read coverings in the underlying site. The existential
  `hcont` and `hlim` express that its sheaf inverse image preserves finite limits.
- The topoi inverse-image square is the natural isomorphism `e`, between restriction
  followed by localized inverse image and inverse image followed by restriction.
  Composition is written in Lean's left-to-right functor order.
- The ring inverse-image comparison is `eR` with the same functors on commutative
  rings. The witness `aV` is the adjunct of the localized coefficient map. Its first
  equation says that on every `T : Over V`, its component is exactly the component
  of the adjunct of c at `T.left`. Its second equation specifies that the localized
  coefficient map is `eR.hom.app R` followed by restriction of c. Thus the ringed
  square commutes with precisely the prescribed ring map, not an arbitrary map.
- Module functors use Mathlib `SheafOfModules.pushforward` with the forgotten
  commutative-ring adjunct and `SheafOfModules.pullback` with that same adjunct.
  The former is precomposition with scalar restriction through the adjunct.
  The latter is its specified left adjoint. The recorded module-adjunction theorem
  identifies this with `S ⊗_(f⁻¹R) f⁻¹M` and its canonical tensor adjunction;
  this is an existing unique-up-to-isomorphism construction, not a replacement
  definition of tensor pullback. Restriction is `overFunctor`, whose ring map is
  the identity, so the same adjunction identifies it with localization pullback.
- The `Nonempty` natural isomorphism renders `(f_V)^* j_V^* ≅ j_U^* f^*`.
  The natural isomorphism `eM` renders `j_V^* f_* ≅ (f_V)_* j_U^*`.
  Its final equation, quantified over every module G, slice object T and section x,
  reads `((eM.hom.app G).val.app (op T)) x = x`. It fixes exactly the sectionwise
  identity `G(u(T)) = G|_U(u(T)→U)`. Since these components are module morphisms,
  they are linear for the restricted R(T)-action; that action is fixed by the
  preceding equation for `aV` and Mathlib's pushforward construction.

Dependency declarations read and used:

- `def-weil-pbc-sites-and-cohomology`: Mathlib `Precoverage` and its site-axiom
  classes, `Precoverage.toGrothendieck`, `Sheaf`, `Functor.IsContinuous`, and
  `Functor.sheafPushforwardContinuous`; inverse image and adjunction from
  `Mathlib.CategoryTheory.Sites.Pullback`. The recorded H' and cohomology clauses
  are irrelevant to this localization statement.
- `def-pur-localized-ringed-site`: `GrothendieckTopology.over`, `.overPullback`
  and `Sheaf.over` in `Mathlib.CategoryTheory.Sites.Over`; `SheafOfModules.overFunctor`
  and `.over` in `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.
- `lem-weil-pbc-slice-site-localization`: `CategoryTheory.slice_site_localization`
  in `Sheaf.Paper.SliceSiteLocalization`, imported publicly; its exact site hypotheses
  and slice comparisons are used for the underlying morphism.
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules` in
  `Sheaf.CategoryTheory.RingedSiteModules` is transparently `SheafOfModules`;
  the statement uses that underlying Mathlib category directly.
- `def-pur-sheaf-tensor-product`: `SheafOfModules.changeOfRings`,
  `changeOfRingsPresheaf`, `changeOfRingsHom` and the tensor/sheafification
  identification in `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`.
- `lem-weil-pbc-ringed-topoi-module-adjunction`:
  `SheafOfModules.module_pullback_pushforward_adjunction` in
  `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`. This and the tensor
  module are proof imports: together they identify the adjoint pullback with the
  node's tensor formula and supply the Hom argument in step 3 of the docstring.

Additional Mathlib imports `Ring.Colimits`, `Ring.FilteredColimits`, `Ring.Limits`
supply the commutative-ring sheafification and inverse-image adjunction instances.
`ModuleCat.Sheaf.PullbackContinuous` supplies the module functors and adjunction.
All parameters and the universe are explicitly bound; `autoImplicit` is false.

Edge cases checked before drafting: empty sites have no V, so the assertion is
vacuous there without a Nonempty assumption; initial/empty slice objects and empty
coverings are retained; no binary products of the whole site or subcanonical topology
are assumed. Zero rings and zero modules are allowed by CommRingCat and SheafOfModules;
no nontriviality or characteristic restriction occurs. The identity site morphism
and V a terminal object give the expected restriction comparisons. In the section
comparison, both sides have definitionally the carrier `G(u(T.left))`; linearity
uses the explicitly equal adjunct components, not an unidentified coefficient action.

Searches for an existing statement:

- msearch leanfinder, query “Localization of morphism of ringed sites module pullback
  restriction commutes direct image”: eight hits, including pullbackFree lemmas and
  Scheme.Modules.restrictFunctorIsoPullback; none states the ringed slice square.
- msearch loogle, query `SheafOfModules.pullbackComp, SheafOfModules.overFunctor`:
  zero hits. The local sources of both existing constructions were then read.
- msearch grep, query `localiz.*[Rr]inged|over.*[Pp]ushforward` in
  `Algebra/Category/ModuleCat`: nine hits on restriction and its adjunctions,
  no localization of an arbitrary ringed site morphism.
- msearch leansearch, query “localization morphism ringed sites commutes module pullback
  direct image”: service unavailable, Internal Server Error.
- rg in the upstream WeilConjectures tree and project lean/Sheaf for localization
  of ringed morphisms and over/pushforward: no matching theorem. The existing
  SliceSiteLocalization module covers only the unringed result. grep of the item id
  in upstream WeilConjectures: no hits. Exact proposed-name search in Mathlib,
  upstream, project and dag/lean_names_upstream.json: no collision.

Sources read: local Stacks `sites-modules.tex` lemma-localize-morphism-ringed-sites
(Tag 04J0), including its proof; `sites.tex` lemma-localize-morphism (Tag 03CF),
including the sectionwise direct-image computation. The statement follows these
sources and the node without a correction or disputed-statement flag.

Validation: server-only scompile.py, nice 19, two threads, 60 seconds per file.
The delivered file compiled cleanly in 3.9 seconds after resolving the required
commutative-ring instances and making the module coefficient parameters explicit.


## Second reading by NP

Independent second reader: read the node and the complete delivered signature, Stacks
sites-modules.tex lemma-localize-morphism-ringed-sites (04J0), and sites.tex
lemma-localize-morphism (03CF), including their surrounding sections and proofs.
There are no new definition nodes, dependency replacements, or statement corrections
in this delivery. No mathematical mismatch was found; the Lean and node are retained.

Object, hypothesis and conclusion checklist (in node order):

1. Small sites D and C: `{D C : Type u} [SmallCategory D] [SmallCategory C]`,
   `K J : Precoverage ...` and HasIsos, IsStableUnderComposition,
   IsStableUnderBaseChange, HasPullbacks on each. Verdict: exact site axioms of
   def-weil-pbc-sites-and-cohomology, including existence only of the covering
   pullbacks, not all pullbacks or binary products of the site.
2. Continuous functor defining f: `u : D ⥤ C`, `hcover`, `hpullback`,
   `[u.IsContinuous ...]`, and `[PreservesFiniteLimits (u.sheafPullback (Type u) ...)]`.
   Verdict: the two explicit continuity clauses are precisely Stacks continuity;
   IsContinuous is its sheaf-preservation consequence, not a different additional
   geometric condition. The left adjoint exists by small-site sheafification and
   Kan extension; its finite-colimit preservation follows from adjunction, so no
   exactness hypothesis has been dropped. No geometric condition beyond the node.
3. Commutative ring sheaves and coefficient map: `R : Sheaf K.toGrothendieck
   CommRingCat`, `S : Sheaf J.toGrothendieck CommRingCat`, and the displayed
   `c : (u.sheafPullback CommRingCat ...).obj R ⟶ S`. Verdict: correct direction
   and coefficient categories. This ring inverse image is the algebraic lift of
   the set inverse image; the ring adjunction's `homEquiv R S c` is its adjunct.
4. Object V and U=u(V): `(V : D)` and `u.obj V`; slices `Over V` and
   `Over (u.obj V)`, topologies `.over`, rings `R.over V`, `S.over (u.obj V)`.
   Verdict: literal localized sites and restricted rings of the dependency, not
   an open subsite, subcanonical replacement, or a scheme-specific construction.
5. Localized functor and morphism: `Over.post (X := V) u`; first conjunct
   preserves covering presieves via `Presieve.overEquiv`; second preserves their
   pullbacks; witnesses `hcont` and `hlim` give continuity and finite-limit exactness
   on sheaves. Verdict: all clauses of the induced site morphism, with the same
   covering-pullback scope as the hypotheses.
6. Inverse-image square: natural isomorphism `e` from restriction followed by
   slice inverse image to inverse image followed by restriction. Verdict: the
   node's square, with compositions translated to Lean's left-to-right order.
7. Ringed square: `eR` is the same comparison for ring sheaves; `aV` is a ring
   sheaf morphism on the localized base. Its section equation identifies each
   component with the original adjunct at T.left; its adjunction equation is
   exactly the adjunct of `eR.hom.app R ≫ ...map c`. Verdict: the prescribed
   restricted coefficient map and its scalar action, rather than arbitrary data.
8. Module categories and functors: `SheafOfModules` on the forgotten ring sheaves,
   `overFunctor` for restriction, `pushforward` for precomposition with scalar
   restriction through the explicitly displayed adjunct, and its `pullback` left
   adjoint. Verdict: these are the recorded general-site constructions. The
   tensor formula is identified with this adjoint by the recorded tensor/module
   adjunction dependency; no private module-pullback definition is introduced.
9. Module pullback square: `Nonempty (overFunctor ... ⋙ pullback ... ≅
   pullback ... ⋙ overFunctor ...)`. Verdict: the natural isomorphism
   (f_V)^* j_V^* ≅ j_U^* f^*, with the coefficient map from item 7.
10. Module direct-image square: witness `eM` between `pushforward ... ⋙
    overFunctor ...` and `overFunctor ... ⋙ pushforward ...`. Verdict: exactly
    j_V^* f_* ≅ (f_V)_* j_U^*, not the different right-adjoint square involving j_*.
11. Direct-image components: `∀ G T x, ((eM.hom.app G).val.app (op T)) x = x`.
    Verdict: sectionwise identity G(u(T)) with precisely the restricted R(T)-action,
    since these are module morphisms and item 7 fixes the scalar homomorphism.
    Quantifiers put the comparison before G,T,x, so it is one natural comparison.

Dependency audit: opened SliceSiteLocalization.lean and its complete theorem
signature; it gives the underlying morphism and both unringed comparisons. Opened
RingedSiteModules.lean: its abbreviation is transparently Mathlib SheafOfModules,
so using that underlying category does not create or substitute a notion. Read the
module-adjunction signature and proof docstring in ModulePullbackPushforwardAdjunction,
and changeOfRingsPresheaf/changeOfRings in TensorProduct.lean: they use sheafified
sectionwise scalar extension and identify the tensor-formula left adjoint.
Read Mathlib Sites/Pullback.lean (the chosen adjoint and its sheafification/Kan
construction), Sites/Over.lean (covering sieves and restriction), and
ModuleCat/Sheaf/PushforwardContinuous.lean and PullbackContinuous.lean (sectionwise
pushforward, overFunctor, chosen left adjoint and pullbackIso). Their signatures
apply to the exact sites and rings here; smallness supplies the construction
instances, not an added existence assumption. The localized-site node's Mathlib
matches are the general over topology and sheaf/module restriction just read.

Edge cases: an empty D has no V and the theorem is vacuous; no Nonempty site,
nonempty covering or terminal object is required. Empty slices/initial objects
are not excluded. Empty finite limits are included in PreservesFiniteLimits.
Zero rings and zero modules are allowed; no Nontrivial or characteristic binder,
Noetherianity, finiteness or scheme hypothesis occurs. No numerical parameter or
index set occurs. The ambient universe u is arbitrary and shared by small sites,
rings and module values, exactly the small-site-relative-to-values encoding;
there is no smaller independent universe of test objects. Every variable and
universe is explicitly bound with autoImplicit false.

Independent searches (different queries from the author):
- LeanFinder via msearch: "Sheaves of modules restriction to slice site commutes
  with direct image along a continuous functor" returned eight hits, chiefly
  Scheme.Modules.restrictFunctorComp/restrictFunctorIsoPullback and dense-subsite
  restriction. These specialize to schemes/open immersions or another comparison,
  and do not state this general ringed-site localization result.
- Loogle via msearch: `"SheafOfModules", "pushforwardNatIso"` returned three
  pushforwardNatIso declarations. Read their source in PushforwardContinuous:
  they transport pushforward along an isomorphism of site functors, not this
  localized inverse-image/ring/module square.
- LeanSearch via msearch: "Restriction of sheaves of modules to localized sites
  commutes with pullback and pushforward": unavailable, Internal Server Error.
- Independent rg of upstream WeilConjectures, project lean/Sheaf and Mathlib's
  ModuleCat for `localiz.*ringed|ringed.*localiz|overFunctor.*pushforward|pushforward.*overFunctor`:
  no theorem with the full statement; project hits concern individual restrictions,
  ringed spaces or scheme specializations. Existing pullbackComp supplies one
  proof ingredient but does not already state this node.

H5/H6/H8/H9: one named theorem only, proof exactly `by sorry`; no definitions,
private copies, local instances or local notation. Module and theorem docstrings
carry 04J0/03CF and the blueprint id. All three node proof steps, including the
coefficient compatibility and Hom-adjunction argument, are in the theorem docstring.
The stored lean.statement was checked programmatically to equal the signature
verbatim. No Lean or node changes were necessary; this independent review is the
only addition. Validation uses the required server-only scompile.py at the normal
60-second per-file limit, nice 19 and two threads; delivery dry run follows below.
