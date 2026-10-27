## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleLineFrameTransitionUnits` states
`AlgebraicGeometry.Scheme.etale_line_frame_transition_units`, with `sorry` as its
whole proof. Its five auxiliary declarations abbreviate localized frames,
evaluate changes of frames, package the existing canonical tensor-unit map as an
isomorphism, pull unit automorphisms back in these coordinates, and express an
actual ordinary overlap isomorphism in these coordinates. Their data is fully
constructed; no additional postponed theorem or new notion is introduced.

The source was read in `literature/stacks-project/descent.tex`, proposition
`proposition-equivalence-quasi-coherent`, Tag 03DX (2), especially its overlap
isomorphisms, omitted cocycle verification, and final small-site paragraph. The
node supplies the elementary rank-one proof in full, reproduced step by step in
the theorem docstring. No node statement correction is necessary.

Hypothesis and clause correspondence:

* The scheme is `(X : Scheme.{u})`, Mathlib's recorded scheme type. The explicit
  universes are `u w`; the covering index is arbitrary `(I : Type w)`. No
  nonemptiness, finiteness, affine, separatedness or Noetherian hypothesis occurs.
* The small etale site is `X.Etale` with `X.smallEtaleTopology`. Objects have
  structure map `U.hom` and all morphisms are X-morphisms. Products in this
  category are scheme fibre products over X. `Limits.prod (U a) (U b)` is R_ab;
  the left-associated triple product is the displayed triple overlap.
* O_et is the existing `X.etaleStructurePresheaf`, taking an object W to
  `Γ(W.left, ⊤)`, followed by `forget₂ CommRingCat RingCat`. Module-sheaf G is
  supplied as `(G : _root_.PresheafOfModules ... )` and
  `(_hG : Presheaf.IsSheaf X.smallEtaleTopology G.presheaf)`. These are exactly
  the `val` and `isSheaf` fields of the dependency's Mathlib `SheafOfModules`;
  they are not a different module category or a private copy. In particular,
  module maps are Mathlib's linear natural maps, without extra restrictions.
  This field presentation avoids the unnecessary universe constraint caused by
  the general `sheafCompose` limit-preservation instance on this large site.
  It does not assume an extra sheaf condition on the structure presheaf.
* The family is `(U : I → X.Etale)` and the hypothesis is
  `(_hU : X.smallEtaleTopology.CoversTop U)`. On this site it is precisely
  joint surjectivity: `CoversTop` says its objects generate a covering sieve of
  the terminal object, which is the identity X, and
  `ofArrows_mem_smallEtaleTopology_iff` identifies this with the union of the
  images being all of X. No restriction on the size of I relative to u is used.
* The frames are `(t : ∀ a, TrfEtaleFrame G (U a))`. This abbreviation uses the
  over category and `PresheafOfModules.pushforward₀ (Over.forget U)` to restrict
  G by precomposition. A source object `W → U` has exactly the ring Γ(W,O_W).
  The over category is the localized small etale site: an etale scheme over
  U is etale over X, and any X-morphism between etale X-schemes is etale.
  The sheaf-to-module-presheaf functor is fully faithful, so this presheaf
  isomorphism is precisely a module-sheaf frame, with its full naturality.
* The conclusion `∃! g : ∀ a b, Γ(R_ab, ⊤)ˣ, ...` asserts existence and
  uniqueness of the unit family. The first conjunct quantifies over every
  `W : X.Etale`, every `q : W ⟶ R_ab`, and every `s : Γ(W.left, ⊤)`.
  `trfEtaleFrameChange (t a) (t b) (q ≫ prod.fst) (q ≫ prod.snd) s`
  evaluates t_a inverse after t_b at the same underlying G(W). Its equality
  to `s * q.left.appTop (g a b)` is the required action on every etale test.
* The next conjunct gives both evaluation formulas: the underlying unit is
  `trfEtaleFrameChange (t a) (t b) prod.fst prod.snd 1`, and its inverse value
  is the reverse change `trfEtaleFrameChange (t b) (t a) prod.snd prod.fst 1`.
  Identity of R_ab is implicit here in evaluating directly on its projections.
* The next conjunct is the unit-valued cocycle. Its three `Units.map` terms
  use p_ab = prod.fst, p_bc = prod.lift (prod.fst ≫ prod.snd) prod.snd,
  and p_ac = prod.lift (prod.fst ≫ prod.fst) prod.snd from (U_a×_XU_b)×_XU_c.
  The equation has exactly the order p_ab^*g_ab * p_bc^*g_bc = p_ac^*g_ac.
* Diagonal normalization is a separate conjunct using
  `prod.lift (𝟙 (U a)) (𝟙 (U a))` and `Units.map ... (g a a) = 1`.
  There is no assertion g_aa=1 on the entire overlap.
* The existential `φ` consists of actual ordinary module isomorphisms from
  `(Modules.tensorPullback prod.snd.left).obj (SheafOfModules.unit U_b.ringCatSheaf)`
  to the corresponding pullback along prod.fst from U_a. This is the required
  b-to-a orientation, using the recorded tensor pullback, not etale pullback.
* The first predicate on φ says, on every Zariski open V of R_ab and every
  section s, that `trfFrameOverlapCoordinates (φ a b)` sends s to the product
  with the restriction of g_ab. This identifies φ with multiplication by g_ab
  under the canonical tensor-unit identifications. The coordinate definition
  is theta_b inverse, then φ, then theta_a (Lean's left-to-right `≪≫`).
* The two remaining predicates assert the ordinary cocycle and diagonal
  normalization in precisely these tensor-unit coordinates.
  `trfFramePullUnit v` is theta_v inverse, pullback of the automorphism, then
  theta_v. Thus the composite first applies p_bc^*φ_bc, then p_ab^*φ_ab,
  and equals p_ac^*φ_ac after the stated unit identifications. The diagonal
  is the identity of the ordinary structure module on U_a. These equations
  are the descent equations expressed on one common unit object, including
  the canonical identifications for iterated tensor pullback; no arbitrary
  comparison isomorphism is assumed.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (def-pc-scheme).
* `Mathlib.AlgebraicGeometry.Sites.Etale` and its public imports:
  `AlgebraicGeometry.Scheme.smallEtaleTopology`, `Scheme.Etale`, and its
  finite limits (def-weil-pbc-etale-site).
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  is transparently Mathlib `SheafOfModules`. The statement supplies its two
  fields directly; `SheafOfModules.Hom`, `fullyFaithfulForget`, and the
  underlying `PresheafOfModules` justify this exact presentation
  (def-weil-sheaf-of-modules-category). The recorded dependency module is
  publicly imported.
* `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` publicly exposes
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` and the normalized
  adjunction and composition interfaces (def-pc-module-pullback).
* `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  `Modules.tensorPullbackObjUnitToUnit` and
  `Modules.tensorPullbackObjUnitToUnit_isIso`. The helper `trfFrameTensorUnit`
  is only `asIso` of this existing canonical map. Its source uses the
  section-normalized `exists_tensorPullbackAdjunction`, rather than an
  arbitrary adjunction. The helper is not a second tensor construction.
* `WeilConjectures.AlgebraicGeometry.Sites.Gm`:
  `Scheme.etaleStructurePresheaf`. The ring and restriction maps are Γ and
  pullback of functions, exactly as required.
* `Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward`:
  `PresheafOfModules.pushforward₀` and `PresheafOfModules.unit` for localized
  frame sources and targets. Explicit universe annotations and an arbitrary
  index universe implement def-weil-size-convention, which records no object.

Edge cases checked mathematically before finalizing:

* Empty I is allowed, as is the empty scheme; on a nonempty scheme the empty
  family fails the covering hypothesis. For an empty index the unit and
  overlap families are empty functions, with their expected uniqueness.
* Empty overlaps have the zero global ring. Its single unit is valid; no
  nontrivial-ring or nonempty-space condition was inserted.
* Repeated indices do not force g_aa=1 away from the diagonal. The two
  projections from U_a×_XU_a need not coincide. Only the diagonal is normalized.
* Identity covers reduce to the usual change of two line-module frames.
* The uniqueness of the whole family is equivalent to the pairwise uniqueness
  in the node: the first action conjunct alone determines every g_ab by
  evaluation at the overlap identity and 1. The extra cocycle clauses do not
  weaken that uniqueness assertion.
* No characteristic, rank certificate, quasi-coherence or line-bundle
  hypothesis is added: the supplied frames already express local rank one.
* G's module sections are in u, the same universe as Γ. This excludes no
  framed object up to the project's size convention: every test object has
  a u-small set of sections, since it maps to a u-small scheme with an
  etale cover by the given frames, each with section module Γ; descent is
  a subobject of a u-small product. The index I remains independently large.

Searches for an existing statement and canonical constructions:

* `msearch.py`, LeanFinder: "Etale frames of a line module give unique units
  on overlaps satisfying cocycle and diagonal identities" (record in
  searches.jsonl, 2026-10-23): 8 hits, etale ring presentations and local-frame
  coefficient equality, no full statement.
* `msearch.py`, Loogle: `"SheafOfModules", "unit"`: 12 hits, unit presheaves,
  evaluation and free adjunctions, no overlap descent theorem.
* `msearch.py`, Mathlib grep:
  `[Ff]rame.*[Cc]ocycle|[Tt]ransition.*[Uu]nit|[Ee]tale.*[Ll]ine`: 2 etale
  Kahler hits, no match.
* `msearch.py`, LeanSearch: "Automorphisms of a module structure sheaf are
  multiplication by global units and line frames yield a cocycle": 8 hits,
  including `SheafOfModules.unitHomEquiv_apply_coe`, `LinearEquiv.smulOfUnit`,
  and group cohomology cocycle constructors, no etale-to-ordinary assertion.
* `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: the item id, proposed declaration names,
  frame/cocycle and transition/unit patterns give no exact existing theorem.
  `grep -rn` for the item id in `lean/WeilConjectures` found no declaration.
  Searches for tensor-pullback unit identifications found the canonical
  `tensorPullbackObjUnitToUnit` map and its proved isomorphism theorem, used
  here rather than rebuilding that map.

Validation: prescribed `scompile.py NE lem-trf-etale-line-frame-transition-units`
compiled this single module in both sandbox and library mode without any errors
or warnings (55.5 s and 27.1 s in the final pre-delivery check). All variables and
universes are explicitly bound; both auto-implicit options are false. The only
postponed theorem is the named main theorem. No STATEMENT-DISPUTED issue remains.

## Second reading by NE

This is the dispatched author's second reading; the maintainer supplies the
independent review. I reopened the node and compared the final signature with
all clauses. The original draft had a tautological last conjunct giving the
expansion of an overlap-map definition. I removed that conjunct and changed the
ordinary existential to quantify actual b-to-a isomorphisms φ. Their unit
coordinates carry the multiplication formula and the two descent equations.
Thus the final signature exposes the ordinary descent maps themselves and
contains no extra defining-equality conjunct.

I checked the cover binder (arbitrary index and CoversTop), the exact two-field
module-sheaf presentation, localized frame sources and targets, and the order
of frame composition. I checked that the first predicate tests every etale map,
that the next predicate includes both evaluations, and that the triple-unit
and diagonal-unit equations use the correct maps. I checked every occurrence
of the ordinary φ source and target, the direction of theta_b inverse followed
by φ followed by theta_a, the reverse composition order of the ordinary
cocycle in Lean's left-to-right notation, and the diagonal identity. None
identifies the two projections of a repeated-index overlap. The helpers have
real data and use the existing canonical tensor-unit morphism. No node or
statement dependency was changed, and no missing clause, extra hypothesis,
new node, or dependency interface repair was found in this final reading.
