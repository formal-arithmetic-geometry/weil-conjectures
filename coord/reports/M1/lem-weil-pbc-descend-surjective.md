## Worker report

The module `Sheaf.AlgebraicGeometry.DescendSurjective` states
`AlgebraicGeometry.exists_surjective_of_isLimit`, with proof `by sorry`.
It introduces no definitions. The node copy changes only `lean`.

Source checked: https://stacks.math.columbia.edu/tag/07RR and
https://stacks.math.columbia.edu/tag/081D. The local literature/stacks-project/limits.tex
is absent on this machine, so the official tag pages were opened instead.
The seven-step proof in the node is reproduced in the declaration docstring.
No statement correction, disputed statement, or dependency fault was found.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Directed set: `{I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]`.
  The index universe v and scheme universe u are independently bound.
- Inverse system of schemes: `D : Iᵒᵖ ⥤ Scheme.{u}`. The functor supplies identities
  and the transition composition law; opposites give the inverse-system direction.
- Affine transition morphisms:
  `[∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]`.
- Limit S: `c : Cone D` and `_hc : IsLimit c`; S is c.pt and its projection to S₀
  is `c.π.app (op i₀)`. An arbitrary limiting cone covers every choice of limit,
  rather than imposing a particular construction from the existence theorem.
- Chosen index 0: `(i₀ : I)`; this is a distinguished index, with no arithmetic
  zero or least-element assumption. It already rules out an empty I.
- S₀ quasi-compact and quasi-separated: `[CompactSpace (D.obj (op i₀))]` and
  `[QuasiSeparatedSpace (D.obj (op i₀))]`.
- X₀ and Y₀ over S₀ and f₀ a morphism over S₀:
  `(X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)`. Their structure morphisms
  are X₀.hom and Y₀.hom, and f₀'s over-category condition imposes their compatibility.
- X₀ quasi-compact and quasi-separated: `[CompactSpace X₀.left]` and
  `[QuasiSeparatedSpace X₀.left]`.
- Y₀ quasi-compact and quasi-separated: `[CompactSpace Y₀.left]` and
  `[QuasiSeparatedSpace Y₀.left]`.
- f₀ locally of finite presentation: `[LocallyOfFinitePresentation f₀.left]`.
  No extra finite-presentation, quasi-compact-morphism, or separatedness assumption
  is inserted.
- Base change f to S and its surjectivity:
  `_hf : Surjective (((Over.pullback (c.π.app (op i₀))).map f₀).left)`.
  By the definition of Over.pullback its objects have underlying schemes
  `pullback X₀.hom (c.π.app (op i₀))` and
  `pullback Y₀.hom (c.π.app (op i₀))`; its map is the canonical induced map
  between those fibre products.
- Some i ≥ 0 and the base change fᵢ surjective:
  `∃ (i : I) (hi : i₀ ≤ i),
  Surjective (((Over.pullback (D.map (homOfLE hi).op)).map f₀).left)`.
  `homOfLE hi : i₀ ⟶ i` and its opposite give Sᵢ → S₀, so this is exactly the
  same base-change construction at a finite stage.

Dependency declarations read and used:

- def-pc-scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`, including their full signatures/docstrings.
- pqf-def-affine-morphism: `AlgebraicGeometry.IsAffineHom` in
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`.
- lem-weil-pbc-limit-affine-transition: imported
  `Sheaf.AlgebraicGeometry.LimitAffineTransition`; read
  `AlgebraicGeometry.exists_limit_affine_transition` and its full proof docstring.
  That theorem gives the existence of the limiting cones represented here by c and hc;
  its `Cone`/`IsLimit` representation is used, without redeclaring the existence theorem.
- def-weil-pbc-scheme-conventions: its lean record is explicitly a convention, with
  no declaration/module of its own. The listed Mathlib `CompactSpace` and
  `QuasiSeparatedSpace` instances implement the qcqs scheme conditions.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, `pullback.lift`, and `pullback.map` in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  `CategoryTheory.Over.pullback`, read in full in
  `Mathlib.CategoryTheory.Comma.Over.Pullback`, bundles precisely these fibre products
  and their canonical maps; it does not define another notion.
- def-weil-surjective-morphism: `AlgebraicGeometry.Surjective` in
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
- def-sbc-locally-finite-presentation: `AlgebraicGeometry.LocallyOfFinitePresentation`
  in `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.

Edge cases checked: no empty index set is inadvertently required (i₀ is given);
preorders with equivalent distinct indices are allowed; no strict inequality is
required and i = i₀ is permitted; singleton diagrams are included. Empty schemes
are allowed, with no Nonempty hypothesis on X₀, Y₀, or S. In particular empty Y
has vacuous surjectivity, while the conclusion still requires a stage with the
actual base-change map surjective. No characteristic, nonzero-ring, integral,
affineness-of-stages, or affine-X₀/Y₀ restriction is imposed. Only S₀, X₀, Y₀
are assumed qcqs, as the node and source say. There are no test-object universe
hypotheses, and the diagram universe is independent of the scheme universe.

Searches made (all on 2026-10-11; raw msearch results in searches.jsonl):

- LeanSearch via msearch.py: query “surjectivity descends to a finite stage for a
  locally finitely presented morphism over an inverse limit of schemes”. Service
  unavailable: Internal Server Error; no verdict drawn from that search.
- LeanFinder via msearch.py: query “surjectivity descends to a finite stage of an
  inverse limit of schemes with affine transitions and locally finitely presented
  morphism”. Eight hits: affine-space projections, pointsPi surjectivity, existence
  of affine covers, affine target image ring maps, and an equality-descent theorem
  for morphisms of finite type. None states this lemma.
- Loogle via msearch.py: `AlgebraicGeometry.Surjective,
  AlgebraicGeometry.LocallyOfFinitePresentation`. Five hits about fppf/fpqc descent,
  effective epis and singleton fppf covers; none states this lemma.
- Mathlib grep via msearch.py: `descend.*surject|surject.*[Ll]imit|07RR` in
  AlgebraicGeometry. Fifteen hits about jointly surjective colimit maps and flat
  surjective descent; no 07RR or finite-stage surjectivity theorem.
- rg in WeilConjectures and lean/Sheaf:
  `descend.*surject|surject.*[Ll]imit|07RR|lem-weil-pbc-descend-surjective`.
  Hits concern universal homeomorphisms, fpqc descent, towers of abelian groups,
  colimits of ring maps, and a docstring citing this as-yet-unstated node.
  No duplicate declaration. `grep -rn lem-weil-pbc-descend-surjective` in
  WeilConjectures returned no hits.
- Name collision rg for `exists_surjective_of_isLimit` in Mathlib,
  WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json returned no hits.

Validation: scompile.py on the server succeeded in 1.7 seconds, without warnings.
Every variable and universe is explicitly bound. The theorem proof is only sorry.
deliver2.py --no-push printed OK: the module compiles and passes the preflight
except for the independent second reading, which the second reader writes. Nothing pushed.

## Second reading by M1

I reread the source tags 07RR and 081D, the node statement, all recorded statement dependencies,
and `Sheaf.AlgebraicGeometry.DescendSurjective`. The correspondence is exact:

- The directed index is `{I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]`.
- The inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`; the affine-transition hypothesis is
  `[∀ {i j} (a), IsAffineHom (D.map a)]`.
- The limit is the cone `c : Cone D` with `_hc : IsLimit c`; the distinguished index is
  `(i₀ : I)`.
- Quasi-compactness and quasi-separatedness of `S₀` are the instances on
  `D.obj (op i₀)`.
- `X₀` and `Y₀` are objects of `Over (D.obj (op i₀))`, and `f₀ : X₀ ⟶ Y₀` is their
  morphism over `S₀`; the four qcqs instances on `X₀.left` and `Y₀.left` render the
  hypotheses on those schemes.
- `[LocallyOfFinitePresentation f₀.left]` renders the locally finite presentation
  assumption, with no stronger finiteness or separatedness assumption.
- `_hf : Surjective (((Over.pullback (c.π.app (op i₀))).map f₀).left)` is precisely
  surjectivity after base change to the limiting scheme.
- The conclusion is exactly `∃ (i : I) (hi : i₀ ≤ i), Surjective ...`, with the map
  `D.map (homOfLE hi).op` giving `Sᵢ → S₀` and `Over.pullback` giving the base change.

No mismatch was found and no Lean change was needed. The source's “finite presentation”
wording follows from the stated qcqs and locally finite presentation assumptions, as used by
07RR. The edge cases are covered: `i₀` excludes an empty index, `i = i₀` is allowed,
preorders may have equivalent indices, singleton systems are included, empty schemes and
zero rings are not excluded, and there are no characteristic, integrality, or affineness
assumptions on `X₀`, `Y₀`, or `S₀` beyond qcqs. The index and scheme universes are explicit
and independent, and there are no test-object universes.

I searched Mathlib and the project/source with LeanSearch, LeanFinder/Loogle, and `rg` for
surjectivity descent, `07RR`, and `exists_surjective_of_isLimit`; no existing declaration
states this result. I also checked the dependency declarations and found no unusable
record or private duplicate. Citers `lem-weil-pbc-limit-contained-in-constructible`,
`lem-weil-pbc-affine-etale-site-colimit`, `lem-weil-pbc-finite-surjective-affine-target`,
`lem-weil-pbc-limit-nonempty`, `lem-weil-pbc-constructible-is-image`, and
`lem-weil-pbc-etale-finite-data-descent` continue to use the statement as written.

The module compiles cleanly with `scompile.py`; its only proof is the required `sorry`.

## Reviewer fix (R-dsu1142)

The index type was `{I : Type v}` with an extra universe `v` independent of the schemes'
universe `u`. The recorded limit form (F1 a215660fd, J1 13cd55798, M1 1f76496d8, and
`exists_limit_affine_transition`) takes `{I : Type u}` with `D : Iᵒᵖ ⥤ Scheme.{u}`, so that
the limit exists in `Scheme.{u}`. Fixed to `{I : Type u}` and `universe u` only; the
"independent universes" claims above are superseded. Nothing else changed: the
`Over.pullback (·).map f₀ |>.left` maps are checked by `rfl` to be
`pullback.map X₀.hom g Y₀.hom g f₀.left (𝟙 _) (𝟙 _)`, the recorded fibre-product form.
