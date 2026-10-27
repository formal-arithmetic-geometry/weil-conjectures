## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceSurjectiveAffineLimitCriterion`
states `AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_of_affine_limit_comparison_surjective`.
Its only theorem has proof `sorry`; no definitions, axioms, additional hypotheses,
new nodes, dependency repairs, or statement changes are introduced.

Source checked directly: `literature/stacks-project/spaces-limits.tex`,
`lemma-surjection-is-enough` (Tag 0CM6), including its two successive lifts;
`spaces-morphisms.tex`, `definition-locally-finite-presentation` (Tag 03XP),
and its `lemma-local-source-target` chart criterion. The source agrees with the node.

Clause-by-clause correspondence:

- A scheme S in the stated size convention: `{S : Scheme.{u}}`, with explicit
  `universe u` and `set_option autoImplicit false`. Algebraic spaces over S and
  their morphism: `{X Y : AlgebraicSpace S} (f : X ⟶ Y)`.
- Every small nonempty directed set: `(I : Type u) [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. This uses the published directed-preorder
  convention and the same index universe as the schemes and section sets.
- Every inverse system of affine S-schemes: `D : Iᵒᵖ ⥤ Over S` and
  `∀ i : Iᵒᵖ, IsAffine (D.obj i).left`. No hypothesis on transitions is added:
  every morphism between affine schemes is affine.
- Its limit T and projections: `(c : Cone D), IsLimit c`. The cone vertex
  `c.pt` is T over S; limits in the over category give exactly the inverse
  limits over S, equivalently the underlying scheme limit with its induced
  structural map. No chosen limit or existence witness is made part of the input.
- The filtered colimit of Mor_S(T_i,X) is `colimit (D.rightOp ⋙ X.obj.obj)`;
  the analogous expression for Y is `colimit (D.rightOp ⋙ Y.obj.obj)`.
  Yoneda identifies the points of these sheaves with the indicated morphisms.
  `D.rightOp` reverses the inverse system, so the transitions are restriction.
- `x : X.obj.obj.obj (op c.pt)` is a map T to X, and
  `y : colimit (D.rightOp ⋙ Y.obj.obj)` is the second component of a pair.
  Its fibre-product compatibility is
  `(f.hom.hom.app (op c.pt)) x =
  (colimit.desc (D.rightOp ⋙ Y.obj.obj)
  (Y.obj.obj.mapCocone (coconeRightOpOfCone c))) y`.
  The right-hand map restricts stage sections along the actual cone projections.
- Surjectivity is written elementwise, exactly: there exists
  `z : colimit (D.rightOp ⋙ X.obj.obj)` whose restriction to T is x and whose
  image under `colim.map (Functor.whiskerLeft D.rightOp f.hom.hom)` is y.
  These are precisely the two components of the canonical comparison map.
  This is surjectivity onto the fibre product, without an injectivity assumption,
  an arbitrary map, a stronger stagewise lifting hypothesis, or a new definition.
- Every surjective étale chart V to Y is `V : Over S`,
  `g : yoneda.obj V ⟶ Y.obj.obj`, `IsEtale g`, and `IsSurjective g`.
- Every surjective étale chart U to X ×_Y V is `U : Over S`,
  `h : yoneda.obj U ⟶ Limits.pullback f.hom.hom g`,
  `IsEtale h`, and `IsSurjective h`. This is the presheaf fibre product,
  canonically the underlying presheaf of the sheaf fibre product because
  limits of sheaves are computed on underlying presheaves.
- Its scheme projection U to V is the unique `r : U ⟶ V` characterized by
  `h ≫ Limits.pullback.snd f.hom.hom g = yoneda.map r`. Full faithfulness of
  Yoneda supplies such r for every h, so this equation excludes no chart.
- The conclusion is exactly `LocallyOfFinitePresentation r.left` for all
  these charts. There are no quasi-compactness, quasi-separatedness,
  injectivity, separatedness, or representability hypotheses on f.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-size-convention` is a metatheoretic convention, with no module or
  declaration; explicit universe u, same-universe indices and section colimits
  implement it here.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, and `AlgebraicSpace.IsSurjective`, including their
  full scheme-test definitions and the fppf-sheaf full-subcategory encoding.
- `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`:
  `AlgebraicGeometry.exists_limit_affine_transition`. The interface states
  scheme limit existence; `Cone`/`IsLimit` expresses the limit in this statement.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.desc`, and
  `colim.map`; `Mathlib.CategoryTheory.Limits.Types.Colimits` supplies the
  colimit instances. `Mathlib.CategoryTheory.Whiskering`:
  `CategoryTheory.Functor.whiskerLeft` is the canonical transformation on stage points.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.

Recorded proof-dependency modules imported privately:
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`
(`fibreProduct_isAlgebraicSpace`),
`Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`
(`representable_etale_scheme_tests`),
`Mathlib.CategoryTheory.Limits.Types.Filtered`
(`Types.FilteredColimit.isColimit_eq_iff` and `isColimit_eq_iff'`, alongside
`Types.jointly_surjective` in Types.Colimits),
`Mathlib.AlgebraicGeometry.Morphisms.Etale` (`Etale`), and
`Sheaf.AlgebraicGeometry.LocallyFinitePresentationAffineLimitCriterion`
(`locallyOfFinitePresentation_iff_affine_limit_hom_bijective`).
The affine-transition module is already a public statement import.
`lem-sfb-scheme-surjective-affine-limit-criterion` has no lean record or Mathlib
match in the read clone and its declaration is not needed to state this item;
its future proof import is therefore omitted pending that node's own delivery.

Edge cases checked before writing:

- Empty directed sets are excluded exactly as in the node; singleton and
  non-antisymmetric directed preorders are included. All rings, schemes, and
  indices use u, with no independent smaller universe that could make testing vacuous.
- Empty schemes (including zero-ring affine stages) and empty algebraic spaces
  are permitted. A map to the empty target forces the source empty; the chart
  conclusion is then the ordinary empty-scheme case.
- Constant diagrams use the usual restriction maps and the comparison behaves
  as the identity identification. For identity f the compatible-pair condition
  simply asks for the already specified colimit element.
- Neither U nor V need be affine, quasi-compact, quasi-separated, or nonempty.
  Only the test schemes T_i are affine. Charts and transitions have precisely
  their dependency predicates, with no chosen atlas or arbitrary projection.
- Both preimage equations are required: discarding the colimit-Y equation would
  weaken the hypothesis, and requiring a lift of an exact chosen representative
  at its original stage would strengthen it. The statement does neither.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "For a morphism of algebraic spaces surjectivity of
  the relative affine inverse limit comparison on points implies local finite presentation"`:
  8 hits, headed by `AlgebraicGeometry.LocallyOfFinitePresentation` and its
  affine-open characterization. No relative algebraic-space limit converse.
- `msearch.py ... leansearch "A morphism of algebraic spaces is locally of finite
  presentation if the relative affine directed limit comparison is surjective"`:
  8 hits, scheme local finite presentation, smooth implies lfp, and ring/algebra
  finite-presentation predicates; no exact match.
- `msearch.py ... loogle '"AlgebraicSpace", "FinitePresentation"'`: 0 hits.
- `msearch.py ... grep 'surjectiv.*[Ff]inite[Pp]resentation|[Ff]inite[Pp]resentation.*surjectiv'
  AlgebraicGeometry`: 6 hits, Zariski main, fppf site, and flat descent results.
  None is the affine-limit criterion.
- `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf` for
  `surjection_is_enough`, surjectivity/affine-limit combinations and the exact
  proposed name, and a node-id search in `WeilConjectures`: no exact statement.
  The existing scheme bijective criterion is the relevant proof dependency,
  and the affine-etale descent/finite-etale-tower hits are different statements.
- `dag/lean_names_upstream.json` was searched for the proposed statement name
  and limit-surjectivity names: no matching declaration.

No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by Q91

(Written by the maintainer's independent reviewer, replacing the delivered self-audit
section, which stated that no second reader was started; delivery-errors H11.)

Node statement as a list, against the Lean, against Stacks spaces-limits.tex l.584-593
(Tag 0CM6) and spaces-morphisms 03XP:

1. Scheme S, size convention: `{S : Scheme.{u}}`, one universe u for schemes, indices and
   section sets. Correct.
2. Algebraic spaces X, Y over S and f: `{X Y : AlgebraicSpace S} (f : X ⟶ Y)`, the landed
   def-trf-algebraic-space full subcategory of fppf sheaves; `X.obj.obj` is the underlying
   presheaf on `Over S`, `f.hom.hom` the natural transformation. Correct.
3. Every small nonempty directed set I and inverse system of affine S-schemes:
   `(I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] (D : Iᵒᵖ ⥤ Over S)` with
   `∀ i, IsAffine (D.obj i).left`. Directed preorders instead of posets: the hypothesis is
   quantified over a slightly larger class of systems, but every directed preorder colimit
   is a colimit over a cofinal directed poset, so this is the project's standard convention
   and not a stronger assumption in substance.
4. Its limit T: any `c : Cone D` with `IsLimit c` in `Over S`; for nonempty directed
   (connected) diagrams limits in `Over S` are the scheme limits with the induced
   structure map. Quantifying over all limit cones is equivalent to the node's T.
5. The comparison map and its surjectivity: x ∈ X(T), y ∈ colim Y(T_i) with
   f_T(x) = restriction of y (`colimit.desc` of `Y.mapCocone (coconeRightOpOfCone c)`),
   and ∃ z ∈ colim X(T_i) with restriction x and `colim.map (whiskerLeft D.rightOp f)` image
   y. This is exactly surjectivity onto X(T) ×_{Y(T)} colim Y(T_i); no injectivity, no
   stagewise representative condition. Correct.
6. Conclusion, chart form of 03XP: every V, `g : yoneda.obj V ⟶ Y` étale and surjective,
   every U, `h : yoneda.obj U ⟶ pullback f g` étale and surjective (presheaf pullback = sheaf
   pullback), r the unique map with `h ≫ pullback.snd = yoneda.map r` (Yoneda), and
   `LocallyOfFinitePresentation r.left` (Mathlib, = def-sbc-locally-finite-presentation).
   Not weaker, not stronger; no qc/qs hypotheses.

Edge cases: empty I excluded as in the node; empty schemes/spaces allowed (h, g into the
empty presheaf force U, V empty, conclusion trivial); singleton I gives T = T_i and the
hypothesis is automatic, as in the source.

One definition per notion: def-sfb-space-morphism-properties defines
`MapIsLocallyOfFinitePresentation` (all compatible étale chart pairs). The item node does
not cite it and states its own surjective-chart form, which is one of the equivalent
conditions of Stacks lemma-local-source-target; the inline chart condition is the node's
statement, not a duplicate definition (advisory: a later re-split could cite that node).
Searches: rg for `surjection_is_enough`, `affine_limit`, `MapIsLocallyOfFinitePresentation`
in lean/Sheaf and lean/WeilConjectures: no existing statement of 0CM6.

Records: the item record differs from live only by its `lean` field; `lean.statement`
occurs verbatim in the module; docstrings carry the source place, blueprint id and the
five proof steps; proof is `sorry`; no definitions, no new nodes. The private proof imports
exist in the live tree. No mismatch found in the Lean.
