## Worker report

The node is already stated by the published source module
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`; no duplicate Lean module is
written. The node copy records the existing declarations
`AlgebraicGeometry.Etale.BaseChangeProperty`,
`AlgebraicGeometry.Etale.baseChangeHomologyMap`, and
`AlgebraicGeometry.Etale.UniversalBaseChangeProperty`.

The primary declaration has the exact signature
`def Etale.BaseChangeProperty (p : X ⟶ S) (q : ℤ) : Prop`. Its surrounding
binders are `Λ : Type (u + 1)` with `[CommRing Λ]`, and `X S : Scheme.{u}`.
The body quantifies over `T Y : Scheme.{u}`, `g : T ⟶ S`, `e : Y ⟶ T`,
`h : Y ⟶ X`, instances `[QuasiCompact g]` and `[QuasiSeparated g]`, a
Cartesian square `sq : IsPullback e h g p`, and a sheaf
`F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`. Its conclusion
`IsIso (Etale.baseChangeHomologyMap Λ sq q F)` is exactly the node's
isomorphism condition for every such square and sheaf. There is no
invertibility hypothesis on `Λ`, matching the node.

`Etale.baseChangeHomologyMap` is the component at `F` of
`Etale.baseChangeHomologyNatTrans`. The latter is the derived base-change
morphism `Etale.baseChange`, whiskered by the degree-zero single functor and
then the degree-`q` homology functor. Thus it renders the node's degree-`q`
cohomology sheaf of `Lf^*Rg_* → Rh_*Le^*`, with the adjunction unit, square
transport/pullback exchange, and counit. The source module also supplies
`Etale.baseChangeHomologyMap_naturality`; the adjacent
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality` module supplies
compatibility with étale localization and composition of Cartesian squares.

`Etale.UniversalBaseChangeProperty` has the exact universal quantification in
the node: for `a : S' ⟶ S`, `b : X' ⟶ X`, and `p' : X' ⟶ S'`, with
`IsPullback b p' p a`, it requires
`Etale.BaseChangeProperty Λ p' q`. The cumulative universal clause, including all integer degrees, is exactly
`∀ r : ℤ, r ≤ q → Etale.UniversalBaseChangeProperty Λ p r`. It uses only
the existing universal property, so no new named definition is needed.
For the coefficient notation `BC(f,n,q)`, instantiate the existing ring
parameter with `ULift.{u + 1} (ZMod n)`. The invertibility assumption in
applications is separate from this predicate. The final smoothness observation
is the stability of smoothness under preliminary base change, rather than an
extra condition in the definition; the counterexample sentence refers to the
separate node `sbc-lem-fixed-base-not-universal`.

Edge cases checked from the full signatures: `q : ℤ` is unrestricted (including
negative and zero); `Λ` is any commutative ring (including the zero ring); the
scheme morphism may be arbitrary; empty schemes and sheaves are not excluded;
only squares carrying `IsPullback` are quantified; and the universal
quantifier includes identity and arbitrary base changes. The source uses one
shared scheme universe for all square objects, exactly as recorded.

Searches made on 2026-10-17:

- `msearch.py ... leanfinder "recorded base change property for etale sheaves of modules in one degree and after every preliminary base change"` returned generic étale and ring base-change declarations, with no exact project declaration in Mathlib.
- `msearch.py ... leansearch "The base change property for etale sheaves of modules is invertibility of the degree q base change map for all quasi compact quasi separated morphisms"` returned generic `IsBaseChange`/étale stability results, with no exact property.
- `msearch.py ... loogle "BaseChangeProperty, UniversalBaseChangeProperty"` returned zero hits and unknown identifiers (these are project declarations).
- `msearch.py ... grep "BaseChangeProperty|baseChangeHomologyMap|UniversalBaseChangeProperty"` found the exact declarations in `WeilConjectures/SixFunctors/Etale/SmoothBaseChange/Defs.lean` and their uses in the source; Mathlib had no hits.
- `rg` over `lean/Sheaf` found consumers and the cumulative wrapper, but no duplicate general base-change property.

The node's `lean_audit.slopmaster2` is `closed` for the two original
recorded declarations; the additional universal declaration was read directly.
The item has no statement dependencies. No statement
correction, dispute, dependency module, or new node is needed.

## Second reading by NC

I independently read the node copy and the unchanged repository node, the exact
blueprint source `literature/blueprint/main-20261015/blueprint/sec-smooth-base-change/
sk-def-bc/_section.md`, and Stacks `etale-cohomology.tex`, Remark
`remark-base-change-holds` (Tag 0F02, lines 16848–16865). Stacks quantifies over
both the preliminary base change and the qcqs test morphism and over all degrees
at most the bound. It assumes no smoothness, Noetherian hypothesis, or
invertibility in this definition. The blueprint deliberately distinguishes that
cumulative universal property from fixed-base, fixed-degree BC. I opened the
published `SmoothBaseChange/Defs.lean` in full, the unit/transport/counit
construction in `BaseChangeTheorems/MorphismDefs.lean`, and the relevant
signatures and constructions in `SmoothBaseChange/Locality.lean`.

Object/hypothesis/clause checklist (all verdicts: exact):

1. Arbitrary schemes X and S and their morphism f: section binders
   `{X S : Scheme.{u}}` and `(p : X ⟶ S)` of
   `AlgebraicGeometry.Etale.BaseChangeProperty`. No property of p is assumed.
2. Arbitrary commutative coefficient ring: the section binder
   `(Λ : Type (u + 1)) [CommRing Λ]`. There is no finite, nontrivial, torsion,
   characteristic, or invertibility assumption. The coefficient category is
   `ModuleCat.{u + 1} Λ`, not modules over the structure sheaf.
3. A single integer degree: `(q : ℤ)`; BC does not silently quantify over lower
   degrees or replace q by a natural number.
4. Every qcqs test morphism g: the body quantifies
   `∀ {T Y : Scheme.{u}} (g : T ⟶ S) (e : Y ⟶ T) (h : Y ⟶ X)` with
   `[QuasiCompact g] [QuasiSeparated g]`. These hypotheses are on g only.
5. The Cartesian square: `(sq : IsPullback e h g p)` has exactly
   `e ≫ g = h ≫ p` and the pullback universal property. An arbitrary pullback
   representative Y is equivalent to the displayed fibre product; no choice of
   representative is an extra geometric hypothesis.
6. Every sheaf on the small étale site of T: the body binder is
   `(F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. F is unrestricted.
   Moving this universal quantifier past the independent square data changes
   nothing; no existential choice or naturality assumption is introduced.
7. The specified canonical map: `Etale.baseChangeHomologyMap Λ sq q F` is the
   component of `Etale.baseChangeHomologyNatTrans`, whose actual body is
   `Functor.whiskerLeft _ (Functor.whiskerRight
   (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq) _)`.
   The outer functors are `DerivedCategory.Plus.singleFunctor _ 0` and
   `DerivedCategory.Plus.homologyFunctor _ q`. The source and target functors
   are exactly H^q(p^* Rg_* F[0]) and H^q(Rh_* e^* F[0]). In MorphismDefs,
   `Etale.baseChange` is unit insertion, the pullback square comparison under
   pushforward, and counit contraction. Thus this is the node's derived
   definition itself. Exact inverse image identifies these objects with the
   displayed classical higher-direct-image sheaves; no extra identification
   theorem is needed to *define* the node's map in its chosen derived form.
8. The conclusion is precisely `IsIso (Etale.baseChangeHomologyMap Λ sq q F)`.
9. Universal fixed-degree BC: `Etale.UniversalBaseChangeProperty` quantifies
   over `{S' X' : Scheme.{u}}`, `(a : S' ⟶ S)`, `(b : X' ⟶ X)`,
   `(p' : X' ⟶ S')`, and `IsPullback b p' p a`, and concludes
   `Etale.BaseChangeProperty Λ p' q`. The orientation is the preliminary
   base-change square, and a has no qcqs or other restriction.
10. The general-ring, integer-bound cumulative clause is exactly the Lean
    expression `∀ r : ℤ, r ≤ q → Etale.UniversalBaseChangeProperty Λ p r`.
    The independent universal quantifier over r commutes with the preceding
    square and sheaf quantifiers. This expression uses the existing notion;
    it needs no duplicate definition. I also opened the landed
    `CumulativeUniversalBaseChangeProperty.lean`: its named wrapper is only
    for lifted ZMod coefficients, positive n invertible on S, and natural
    degree bounds, so it must not replace this general-ring expression.
    `UnboundedCumulativeUniversalBaseChangeProperty.lean` likewise concerns
    a different specialized interface. Neither is an exact general match.
11. The coefficient shorthand uses `ULift.{u + 1} (ZMod n)` for a natural
    modulus; an integer modulus uses `n.natAbs`. This is only the size
    convention for Z/nZ. Invertibility remains an application hypothesis,
    not a condition of BaseChangeProperty or UniversalBaseChangeProperty.
12. Naturality is the actual equality in
    `Etale.baseChangeHomologyMap_naturality`. Composition compatibility is
    the equality `Etale.baseChange_app_paste_horiz` in Locality, with its
    degreewise consequence `Etale.isIso_baseChangeHomologyMap_of_paste_horiz`.
    Étale localization is rendered by
    `Etale.isIso_baseChangeHomologyMap_of_etale_cover` there, with the
    specified pullback squares, restrictions, and jointly surjective étale
    family. These clauses are existing map properties, not further
    hypotheses of BC.
13. Fixed-base BC and universal BC stay separate predicates. The explanatory
    counterexample sentence is already isolated as
    `sbc-lem-fixed-base-not-universal` (I opened its node), rather than being
    assumed in this definition. The final smoothness observation uses
    Mathlib's `smooth_isStableUnderBaseChange`: a theorem for *all* smooth
    morphisms applies to every preliminary base change. It does not claim
    that fixed-base BC for one smooth morphism alone proves universal BC.

Edge cases: q = 0 and negative q are included by ℤ; the cumulative expression
also keeps all negative degrees. Zero coefficients, zero sheaves, and empty
schemes are not excluded. There is no indexing set in the predicate; the
localization theorem uses an arbitrary index type and an explicit covering
condition, so an empty cover does not impose nonemptiness on this definition.
The universal quantifier includes identity base changes and arbitrary
non-qcqs preliminary base changes. All scheme objects share the arbitrary
universe u, and the small-site module-sheaf convention uses u+1 for coefficient
rings and module carriers. Smaller rings can be lifted; no field assumption,
site object/morphism universe equality, or unbound universe is added.

Independent searches on 2026-10-17:

- LeanFinder via msearch: `étale sheaf inverse image higher direct image natural
  base change transformation isomorphism property` returned eight generic
  sheaf-of-modules pullback/pushforward isomorphisms, including
  `SheafOfModules.pullbackIso`; none states BC.
- Loogle via msearch: `"baseChange"` returned twelve name hits, including
  `LinearMap.baseChange` and `Submodule.baseChange`; these are scalar
  extension, not the étale predicate.
- LeanSearch via msearch: `An inverse image commutes with the degree q higher
  direct image of every sheaf in every cartesian square with quasi compact
  quasi separated vertical map` returned generic pushforward composition and
  open-immersion identities, with no exact match.
- Independent rg on Mathlib, WeilConjectures, and lean/Sheaf for definitions
  of higher direct images, universal base-change properties, and
  `baseChangeHomologyNatTrans` located the exact three declarations in
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`, plus specialized
  downstream wrappers and unrelated scheme-module higher direct images.
  I checked `dag/lean_names_upstream.json` as well; the source text, not
  similar names in that index, establishes this exact existing match.

No mathematical mismatch or missing dependency was found. There are no new
nodes, dependency modules, statement corrections, or postponed theorems in
this delivery. The existing bodies have real data and no sorry. The existing
upstream source is retained rather than edited to retrofit local docstring
conventions. The node's lean.statement is verbatim the existing declaration
signature, and only the lean field differs from the repository node. There is
no repair note for this item. I changed only this report by adding the
independent source, clause, search, and edge-case audit; the exact existing
binding is retained. Since no Lean module is delivered, there are no sibling
files to compile with scompile.py.
