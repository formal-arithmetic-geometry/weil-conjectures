## Worker report

The module `Sheaf.AlgebraicGeometry.LimitFibreProducts` states
`AlgebraicGeometry.limit_fibre_products_of_affine_transition` with its proof `sorry`.
There are no new definitions, dependency replacements, or statement corrections.

Hypothesis and clause correspondence:
- The directed index set is `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]`.
  The index and scheme universes agree, as required for affine-transition limits.
- The three inverse systems are `X S T : Iᵒᵖ ⥤ Scheme.{u}`. The compatible
  stage maps are natural transformations `f : X ⟶ S`, `g : T ⟶ S`; naturality
  is exactly the commutation with transitions. The three `IsAffineHom` instance
  binders quantify over every transition in each system.
- The specified limits X, S, T are the three cones `cX`, `cS`, `cT` and their
  `IsLimit` witnesses `hcX`, `hcS`, `hcT`. The induced limit maps are `F`, `G`.
  The equations `hF`, `hG` define them by compatibility with every projection;
  they are equations inherent in “the limit morphisms”, not extra geometric assumptions.
- The fibre-product inverse system is the existential functor `P`. Its object
  equalities identify it with the chosen `pullback (f.app i) (g.app i)` at each stage.
  The natural transformations `a`, `b` have components HEq to the actual pullback
  projections. Naturality determines every transition uniquely by both projections,
  hence gives exactly the induced fibre-product transitions. Every `P.map h` is affine.
- The limiting cone `cP` has point equal to `pullback F G`, and both composites of
  each cone projection with a stage projection are HEq to the corresponding limit
  projection composites. Thus its cone maps are exactly the induced maps in the node.
  `Nonempty (IsLimit cP)` states the full universal property, not just an object isomorphism.
- The clause `∀ s : cS.pt` treats every base point. At stage i, `Q.obj i` equals
  `(f.app i).fiber (cS.π.app i s)`, using the node's actual scheme-theoretic fibre.
  The natural transformation `a : Q ⟶ X` has the canonical `fiberι` as components.
  These fibre embeddings are monomorphisms (base changes of the monomorphic
  residue-field point), so naturality uniquely determines the canonical fibre
  transitions, including their induced residue-field maps. All `Q.map h` are affine.
  The cone point is `F.fiber s`; its cone maps commute with the canonical embeddings
  into X through the stated HEq equations, again uniquely specifying them.
  `Nonempty (IsLimit cQ)` is the final fibre-limit clause.

Dependency declarations read and used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`:
  `AlgebraicGeometry.exists_limit_affine_transition`, the existence result for the
  three given cones (used in the natural-language proof, not asserted as an extra conclusion).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`, `pullback.map`; `Mathlib.AlgebraicGeometry.Pullbacks` supplies existence.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `Scheme.Hom.fiberι`.
- `Sheaf.AlgebraicGeometry.LimitResidueField`:
  `AlgebraicGeometry.exists_isColimit_residueField_of_isLimit`, the fibre proof's input.
- `Sheaf.AlgebraicGeometry.FibreProductLimit`: `Scheme.isIso_limit_pullback_comparison`,
  the proof's existing categorical comparison (lem-kun-fibre-product-limits).

Edge cases: empty schemes and fibres impose no point-existence hypothesis; the fibre
clause is vacuous when S has no points. Singleton systems reduce to the usual pullback
and fibre universal properties. Arbitrary characteristics and arbitrary schemes are
allowed; no finiteness, separatedness, or properness assumptions were added. An empty
index set is excluded by `[Nonempty I]`, the standing project convention for
these directed inverse systems, also used in both recorded limit dependencies.
This is essential for the fibre clause: for an empty diagram S is the terminal
scheme Spec Z, but its fibres at prime points are not terminal schemes.

Searches (actual logged calls to msearch.py):
- LeanSearch: “fibre products of inverse limits of schemes with affine transition
  morphisms”: service unavailable (Internal Server Error), no match asserted.
- LeanFinder: “scheme fibre product commutes with inverse limits affine transitions”:
  eight results, including `isAffineHom_π_app` and auxiliary affine-transition cones;
  none states the combined pullback and fibre assertion.
- Loogle: `IsLimit (Cone ?D)`: unknown identifier IsLimit, zero hits.
- Mathlib grep: `pullback.*limit|limit.*pullback` in AlgebraicGeometry: ordinary
  pullback calculations and auxiliary cones, no combined assertion.
- rg over WeilConjectures and lean/Sheaf with limit/fibre/pullback patterns found the
  already recorded `Scheme.isIso_limit_pullback_comparison`, residue-field module,
  and auxiliary `Scheme.exists_pullback_hom_of_isLimit`, not this assertion.
- The item id has no hit in WeilConjectures or dag/lean_names_upstream.json. The new
  declaration name has no hit in Mathlib, WeilConjectures or lean/Sheaf before writing.

Source: local literature sources are absent on this machine; opened the official
[Stacks Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X), whose proof gives exactly
this fibre limit argument and cites Categories 002M. No STATEMENT-DISPUTED issue remains.

## Second reading by F1

I read the node, its Stacks source (Derived Categories, proof of Tag 0G7X at
line 8166), and `LimitFibreProducts.lean` independently. The correspondence is:

- The directed index is `I : Type u` with `[Preorder I] [IsDirected I (· ≤ ·)]
  [Nonempty I]`; the three inverse systems are `X S T : Iᵒᵖ ⥤ Scheme.{u}`.
  This is the nonempty directed-set convention used by the limit and residue-field
  dependency nodes, and the universe is shared with `Scheme.{u}`.
- The compatible diagrams are `f : X ⟶ S` and `g : T ⟶ S`. The three transition
  hypotheses are exactly the three instance binders
  `IsAffineHom (X.map h)`, `IsAffineHom (S.map h)`, and `IsAffineHom (T.map h)`.
- The chosen limits and their universal properties are `(cX, hcX)`, `(cS, hcS)`,
  and `(cT, hcT)`. The limit morphisms are `F` and `G`, with precisely the
  projection equations `hF` and `hG`.
- The first conclusion existentially supplies `P : Iᵒᵖ ⥤ Scheme.{u}`, its two
  projection transformations `a,b`, and a cone `cP`. The object equalities identify
  `P.obj i` with `pullback (f.app i) (g.app i)`; the two `HEq` clauses identify its
  projections with `pullback.fst` and `pullback.snd`; affine transitions are
  `IsAffineHom (P.map h)`; and `cP.pt = pullback F G` with the two stated `HEq`
  projection equations and `Nonempty (IsLimit cP)` gives exactly the limit clause.
  Naturality of `a,b` together with the pullback projection equalities determines the
  induced transition maps, so no weaker unrelated system is admitted.
- The fibre conclusion is `∀ s : cS.pt`, with `Q.obj i = (f.app i).fiber
  (cS.π.app i s)`, `a.app i` equal to `fiberι`, affine `Q.map h`, cone point
  `F.fiber s`, the required projection equation, and `Nonempty (IsLimit cQ)`.
  This covers every point and is the node’s scheme-theoretic fibre statement.

Edge cases checked: empty schemes and empty fibres are allowed; no point-existence,
characteristic, finiteness, separatedness, or properness hypotheses were added;
singleton systems reduce to ordinary pullbacks; `n = 0` is irrelevant; an empty
index is excluded exactly as in the source’s definition of directed set and in both
limit dependencies. The shared universe does not exclude any case in the node.

I repeated the duplicate searches with `msearch.py`, `rg` over Mathlib,
`WeilConjectures`, and `lean/Sheaf`, and checked the upstream name index. The only
matches are the already recorded generic pullback-limit comparison and auxiliary
affine-transition declarations; no declaration states this combined theorem. Thus
there is no existing declaration and no second definition. No mismatch was found and
no source, dependency, or Lean statement was changed. `scompile.py` compiled the
module with no errors or warnings beyond its permitted `sorry` proof.
