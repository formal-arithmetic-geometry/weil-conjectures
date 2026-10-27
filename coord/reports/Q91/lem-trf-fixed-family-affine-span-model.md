## Worker report

Module `Sheaf.AlgebraicGeometry.FixedFamilyAffineSpanModel` states
`AlgebraicGeometry.exists_fixedFamily_affine_span_model`, with `sorry` as its only proof.
There are no definitions, auxiliary theorems, new nodes, or dependency repairs.
Only the item's `lean` record changes; the reviewed Q23 stage-1 statement and split are preserved.
The standing brief's stage-handoff paragraph explicitly allows this stage-2 assignment after
that passing split. The inherited stage-1 BLOCKED ending is therefore inapplicable.
The interrupted sandbox contained only this draft module and search logs, with no node copy
or report; these missing delivery files have now been supplied.

Source read: `literature/stacks-project/limits.tex`, label
`lemma-descend-finite-presentation` (Tag 01ZM), parts (1) and (2), and label
`lemma-descend-affine-finite-presentation` (Tag 01ZN), including its Situation 081D.
Also read `literature/stacks-project/more-morphisms.tex`, label
`lemma-relative-map-approximation-pre` (Tag 0GDX), particularly its paragraph choosing
`X_i ← U_i → Y_i` whose base change recovers the given span before imposing etaleness.
The latest blueprint's `lem-trf-local-term-locality.md` and proof use contracting
correspondences; this auxiliary node preserves its recorded historical provenance and does
not modify that unit statement or route.

Hypotheses and clauses, in statement order:

- A nonempty directed set is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. Using a preorder also includes every directed poset.
  The index and scheme coefficient universe are both `u`, following the project's limit
  convention, with no independent index universe that could invalidate existence of limits.
- The inverse system of affine schemes is `D : Iᵒᵖ ⥤ Scheme.{u}` with
  `[∀ i : Iᵒᵖ, IsAffine (D.obj i)]`. For `hr : i₀ ≤ r`, the transition morphism is
  `D.map (homOfLE hr).op : D.obj (op r) ⟶ D.obj (op i₀)`.
- The specified limit B and its projections are `(L : Cone D) (hL : IsLimit L)`:
  `L.pt` is B and `L.π.app (op i)` is p_i. This allows the supplied limiting cone,
  rather than substituting a chosen isomorphic limit. No separate affineness hypothesis on
  B is imposed: `Scheme.isAffine_of_isLimit L hL` gives it from the affine stages.
- The chosen index and the fixed targets are `(i₀ : I) (P₀ Q₀ : Scheme.{u})`, with
  `[IsAffine P₀] [IsAffine Q₀]`, structure arrows `fP`, `fQ` into `D.obj (op i₀)`,
  and `[LocallyOfFinitePresentation fP] [LocallyOfFinitePresentation fQ]`.
- The given source is `(U : Scheme.{u}) [IsAffine U] (fU : U ⟶ L.pt)` with
  `[LocallyOfFinitePresentation fU]`.
  For these three arrows, local finite presentation is equivalent to finite presentation:
  each source is affine and hence quasi-compact and quasi-separated; each base is affine
  (B by the preceding limit fact), so the arrows are affine and quasi-compact, and are
  quasi-separated. This does not drop the quasi-compact/quasi-separated part of the
  convention node's Stacks 01TP meaning. The same reasoning applies to the output fV.
- The fixed limit targets P_B and Q_B are exactly
  `pullback fP (L.π.app (op i₀))` and `pullback fQ (L.π.app (op i₀))`.
  The given morphisms are `a` and `c` into these objects. Hypotheses `ha` and `hc`
  say their composites with the second pullback projections equal `fU`, precisely
  asserting that they are B-morphisms. Neither arrow has an etale, point, or
  finite-presentation hypothesis.
- The existential `∃ (r : I) (hr : i₀ ≤ r) (V : Scheme.{u})
  (fV : V ⟶ D.obj (op r)), IsAffine V ∧ LocallyOfFinitePresentation fV ∧ ...`
  supplies the later stage, affine source V_r, and its finitely presented structure map.
- The existential arrows `α` and `β` have targets
  `pullback fP (D.map (homOfLE hr).op)` and
  `pullback fQ (D.map (homOfLE hr).op)`, exactly the prescribed P_r and Q_r.
  Their next two equations with `pullback.snd` assert that both are S_r-morphisms.
- The existential `e : pullback fV (L.π.app (op r)) ≅ U` is the requested e_r.
  The equation `e.hom ≫ fU = pullback.snd fV (L.π.app (op r))` makes it a
  B-isomorphism, not an unrelated abstract scheme isomorphism.
- The last two equations express respectively alpha_{r,B} = a composed with e_r
  and beta_{r,B} = c composed with e_r, after projection to P₀ and Q₀. On the
  stage-arrow side, the projection is exactly
  `pullback.fst fV (L.π.app (op r)) ≫ α ≫
  pullback.fst fP (D.map (homOfLE hr).op)`, and similarly for beta.
  On the other side it is `e.hom ≫ a ≫ pullback.fst fP (L.π.app (op i₀))`.
  The B projections agree by the equations over the bases. The cone naturality equation
  identifies p_r followed by S_r → S_i₀ with p_i₀; the two projections thus define
  the actual base change into P_B, uniquely. The pullback universal property makes
  equality of these P₀ projections, together with the already fixed B projection,
  equivalent to the required full arrow equality. This also characterizes the unique
  projection-preserving iterated-fibre-product comparison; no arbitrary comparison
  map or additional hypothesis is introduced. The identical calculation applies to Q₀.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme` (structures and docstrings read).
  Affineness uses Mathlib's `AlgebraicGeometry.IsAffine` and `Scheme.isoSpec`
  in `Mathlib.AlgebraicGeometry.AffineScheme`, as prescribed by the scheme node.
- `pqf-def-affine-morphism`: `AlgebraicGeometry.IsAffineHom` in
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`; its signature requires affineness
  of preimages of every affine open. The instance `isAffineHom_of_isAffine`
  applies to every arrow between affine schemes.
- `def-weil-pbc-category-colimit`: the recorded
  `Mathlib.CategoryTheory.Limits.HasLimits` supplies the dual limit interface.
  `Cone D`, `IsLimit L`, and `L.π` encode the explicit limiting cone. This uses
  the same Mathlib universal-property framework, without copying its definition.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`
  in `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, whose affine-local
  finite-presentation signature and docstring were read.
- `def-weil-pbc-scheme-conventions`: its record explicitly defines no independent
  notion and has no module. Its convention finite presentation = local finite
  presentation plus quasi-compact plus quasi-separated is implemented as explained
  above, using the recorded Mathlib notions, not a new finite-presentation predicate.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd` in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  Scheme pullbacks are supplied by `Mathlib.AlgebraicGeometry.Pullbacks`.
  The signatures and universal-property interface were read.

All available proof dependencies are imported with plain `import`: the qcqs facts from
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`; spreading out from
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`
(`Scheme.exists_isPullback_of_finitePresentation`,
`Scheme.exists_pullback_hom_of_isLimit`, `Scheme.exists_pullback_fst_comp_eq_of_isLimit`);
`AlgebraicGeometry.exists_isAffineHom_baseChange_of_isLimit` from
`WeilConjectures.AlgebraicGeometry.DescendAffine`; and
`AlgebraicGeometry.exists_limit_affine_transition` from
`WeilConjectures.AlgebraicGeometry.LimitAffineTransition`.
Affine permanence and finite-presentation base-change instances are in the public
statement imports. The recorded signatures and docstrings of these project dependencies
were opened. The theorem docstring records all six accepted proof steps and their nodes.

Edge cases checked: a singleton index admits the existing source as model; empty U and
empty target schemes are allowed, with no required rational point or nonempty fibre;
a zero-ring limit is not excluded; transition morphisms need not be surjective, injective
on coordinate rings, or flat. The two arrows can descend at different preliminary stages:
directedness permits a common enlargement. Both targets remain their original prescribed
base changes. There is no characteristic restriction, etaleness assumption, or point.
No statement fault or STATEMENT-DISPUTED issue was found. All variables and the universe
are explicitly bound; `set_option autoImplicit false` enforces this.

Searches actually run via `msearch.py` for Q91 and this item (logged in searches.jsonl):

- LeanFinder: `An affine finitely presented span over an inverse limit of affine schemes
  descends to a common stage keeping two prescribed target models fixed`: eight hits,
  including `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType` and
  `HasAffineProperty.descendsAlong_of_affineAnd`; none constructs the source model
  together with the simultaneous span to the fixed targets.
- Loogle: `"Scheme", "LocallyOfFinitePresentation", "exists"`: one hit,
  `AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`.
  Its full signature and docstring were read at AffineTransitionLimit.lean:1232.
  It factors a map into an already given target; it does not state this item.
- Mathlib grep in AlgebraicGeometry: `span.*descen|descen.*span|exists.*finitePresentation.*model`:
  zero hits.
- LeanSearch: `An affine span of finitely presented schemes descends over a directed
  inverse limit with specified target models`: eight hits, including
  `Scheme.isAffine_of_isLimit`, `Scheme.exists_isAffine_of_isLimit`, and section
  descent. None is the complete statement.
- Direct rg of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id, `fixedFamily`, affine span, and affine_span: no exact item declaration.
  The related landed `FixedFamilyEtaleSpanDescent` concerns additional etale and point
  data, and is not this arbitrary span statement. Direct searches for the proposed
  declaration name and affine-span-model variants in Sheaf and Mathlib found no duplicate.

Validation: the prescribed `scompile.py Q91 lem-trf-fixed-family-affine-span-model`
compiled this module in sandbox and library modes on the server, each in 1.5 seconds,
with exit code zero and no diagnostics. The theorem proof is `sorry`, as stage 2 requires.

## Second reading by Q91

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
