## Worker report

The module `Sheaf.AlgebraicGeometry.ExistsIsSeparatedOverPullbackMap` states
`AlgebraicGeometry.Scheme.exists_isSeparated_overPullbackMap`, with proof `sorry`.
There are no new definitions, new nodes, dependency modules, or statement corrections.

Hypothesis-by-hypothesis and clause-by-clause comparison:

- Directed set I: `{I : Type w} [Preorder I] [IsDirected I (· ≤ ·)]`.
  A preorder is the directed-set convention of Stacks 00D3; no least element is assumed.
- Inverse system of schemes: `D : Iᵒᵖ ⥤ Scheme.{u}`. The functor supplies identity and
  composition compatibility of the transition morphisms.
- Affine transitions: `[∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]`.
- Limit S with its projections: `c : Cone D` and `hc : IsLimit c`; S is `c.pt` and the
  projection to S₀ is `c.π.app (op i₀)`. This takes an arbitrary chosen limit, rather than
  replacing the source system by a particular construction.
- Distinguished index 0: `i₀ : I`. This also entails that the index set is nonempty.
- S₀ qcqs: `[CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]`.
- X₀ and Y₀ schemes over S₀: `X₀ Y₀ : Over (D.obj (op i₀))`, with schemes `X₀.left` and
  `Y₀.left` and structure maps `X₀.hom` and `Y₀.hom`.
- X₀ and Y₀ qcqs: the two `CompactSpace` and two `QuasiSeparatedSpace` instances on their
  underlying schemes. No qcqs requirement is imposed on every stage of D.
- Morphism f₀ over S₀: `f₀ : X₀ ⟶ Y₀`; its underlying morphism is `f₀.left` and the Over
  morphism condition says `f₀.left ≫ Y₀.hom = X₀.hom`.
- X and Y are their base changes to S, and f is the same morphism base changed to S:
  `((Over.pullback (c.π.app (op i₀))).map f₀).left`. The objects are definitionally the
  pullbacks of `X₀.hom` and `Y₀.hom` along that projection; the map is the canonical
  pullback lift, with first component `pullback.fst _ _ ≫ f₀.left` and second component
  `pullback.snd _ _`. Thus this is the base change of f₀ between the specified fibre
  products, not a projection of X alone to S.
- Separatedness of f: the explicit hypothesis `hsep : IsSeparated (...)`.
- Existence of i ≥ 0: `∃ (i : I) (hi : i₀ ≤ i), ...`. The inverse transition to S₀ is
  `D.map (homOfLE hi).op`.
- Xᵢ and Yᵢ are the stated fibre products with Sᵢ, and fᵢ is the base change of f₀:
  `((Over.pullback (D.map (homOfLE hi).op)).map f₀).left`.
- Separatedness of fᵢ: `IsSeparated` of that underlying morphism.
- No finiteness condition on f₀: no locally-finite-type, finite-presentation, or properness
  binder occurs.

Dependency declarations read and used:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (locally ringed spaces locally isomorphic to spectra).
- pqf-def-affine-morphism: Mathlib.AlgebraicGeometry.Morphisms.Affine,
  `AlgebraicGeometry.IsAffineHom` (affine inverse images of affine opens).
- lem-weil-pbc-limit-affine-transition: imported
  Sheaf.AlgebraicGeometry.LimitAffineTransition,
  `AlgebraicGeometry.exists_limit_affine_transition`, whose full signature and proof
  docstring were read. Its conclusion supplies existence of the chosen limiting cone;
  this statement binds such a cone with `IsLimit` and retains the original system.
- def-weil-pbc-scheme-conventions: a convention record with no declaration of its own.
  The qcqs phrases use Mathlib `CompactSpace` and `QuasiSeparatedSpace` as that record
  prescribes. Scheme quasi-separatedness is equivalently quasi-compactness of the diagonal.
- def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and `pullback.lift`.
  Mathlib.CategoryTheory.Comma.Over.Pullback, `CategoryTheory.Over.pullback`, uses precisely
  these chosen fibre products and their canonical map; its full definition was read.
- def-weil-proper-morphism: the record lists `AlgebraicGeometry.IsSeparated` in
  Mathlib.AlgebraicGeometry.Morphisms.Separated, and this is the property used here. Its
  definition is closed immersion of the diagonal. The other listed properties, IsProper
  and UniversallyClosed, are not needed for this separatedness lemma.

Edge cases checked before writing: a singleton directed system gives the original morphism;
`hi` may be reflexive, so i = i₀ is allowed. An empty index set cannot carry the distinguished
index and is already excluded by the node, without an additional hypothesis. Empty schemes
and empty limit schemes are allowed; there is no point, nonempty-scheme, surjectivity, or
field hypothesis. The map f₀ need not be finitely presented. Universes u (schemes) and w
(index set) are separately explicit, and a chosen limiting cone avoids any artificial
small-limit existence assumption. This statement does not quantify over smaller-universe
test schemes or rings. All variables and universes are explicitly bound.

Source checked: local literature/stacks-project/limits.tex is absent on this machine, so
read https://stacks.math.columbia.edu/tag/01ZQ and
https://stacks.math.columbia.edu/tag/081D directly. The hypothesis and conclusion agree
with the node. The source's proof prints the diagonal over S₀; the DAG proof correctly
uses the diagonal of f₀ over Y₀ when f₀ is a general morphism over S₀. The module follows
that DAG proof, with the qcqs and diagonal/base-change checks written out in its docstring.

Searches made (actual remote-service searches logged in searches.jsonl):

- msearch.py leansearch, query `separatedness descends from inverse limit with affine
  transition morphisms to some finite stage`: service unavailable, Internal Server Error.
- msearch.py leanfinder, query `separatedness of base changed morphism descends to a finite
  stage of an inverse limit of schemes`: eight hits on IsSeparated stability under base
  change, composition, projections, Spec, and Proj; no finite-stage descent theorem.
- msearch.py loogle, query `AlgebraicGeometry.IsSeparated`: twelve hits on the definition,
  stability properties, and separated schemes; no finite-stage descent theorem.
- msearch.py grep, query `exists_isSeparated|01ZQ`, subdirectory AlgebraicGeometry:
  zero Mathlib hits.
- rg in WeilConjectures for `exists_isSeparated|01ZQ|descend-separated`: the existing
  `Scheme.exists_isSeparated_pullback_snd` requires locally finite presentation of a
  structural morphism, and descends a morphism to the base, rather than a general morphism
  between two qcqs models. `Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
  also assumes finite presentation and chooses a model. The fixed-base 01ZH statements
  are likewise different. Read the full signatures and docstrings of the nearby 01ZQ
  declarations in WeilConjectures/Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean.
- grep -rn for `lem-weil-pbc-descend-separated` in WeilConjectures: no hits.
- rg in lean/Sheaf for `descend.*[Ss]eparated|exists_isSeparated|IsSeparated.*pullback`:
  only fpqc descent and unrelated applications, no statement matching this node.
- rg in dag/lean_names_upstream.json and WeilConjectures for the item id and
  `exists_isSeparated_overPullbackMap`: no conflicting declaration.

No statement dispute or dependency fault was found. Server compilation and dry-run results
are recorded below when completed.

Validation: scompile.py compiled the module on the server in 1.7 seconds, exit code 0,
with no errors or warnings. Every theorem proof is `sorry`; no proof was supplied.

## Second reading by K1

I reread the node statement, the Lean declaration, the dependency records, and the
source places Stacks Tags 01ZQ and 081D. The item-by-item rendering is:

- A directed index set is `{I : Type w} [Preorder I] [IsDirected I (· ≤ ·)]`;
  this is the Stacks directed-set convention, with no least element assumed.
- The inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}` and its affine transitions are the
  instance `[∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a)]`.
- The limit and projections are the supplied `c : Cone D` and `hc : IsLimit c`,
  with `S = c.pt` and projection `c.π.app (op i₀)`.
- The distinguished index is `i₀ : I`; qcqs of `S₀` is rendered by the two
  instances on `D.obj (op i₀)`.
- `X₀` and `Y₀` over `S₀` are `X₀ Y₀ : Over (D.obj (op i₀))`, with their four
  qcqs instances on `.left`; `f₀` is `f₀ : X₀ ⟶ Y₀`.
- The base-changed limit morphism is
  `((Over.pullback (c.π.app (op i₀))).map f₀).left`; this is the specified base
  change of `f₀` to `S`.
- The separatedness hypothesis is exactly `hsep : IsSeparated (...)` on that map.
- The conclusion quantifies `∃ (i : I) (hi : i₀ ≤ i)` and uses
  `D.map (homOfLE hi).op` as the transition `Sᵢ ⟶ S₀`; its map is exactly
  `((Over.pullback ...).map f₀).left` and its separatedness is `IsSeparated`.

Thus every object, hypothesis, and conclusion clause of the node has a direct Lean
counterpart, with the same quantifier order and no extra finiteness, field,
nonemptiness, or universe restriction. The dependency declarations were checked:
`Scheme`, `IsAffineHom`, the chosen limit cone, fibre products/`Over.pullback`, and
`IsSeparated` are the recorded notions (the conventions node introduces no
predicate of its own).

Edge cases remain covered: `i = i₀` is allowed by reflexivity; an empty index type is
already excluded by the distinguished `i₀`; empty schemes and a zero morphism are
allowed; no characteristic, point, surjectivity, finite-type, or finite-presentation
hypothesis is present; and the index and scheme universes are independent exactly as
the node permits. The source states only the qcqs assumptions on `S₀`, `X₀`, and
`Y₀`, matching the Lean instances.

The existing searches were independently checked in `searches.jsonl`: LeanSearch
(service unavailable), LeanFinder, Loogle, and grep of Mathlib, the source repository,
and `lean/Sheaf` found no declaration of this statement. The nearby source theorem
`exists_isSeparated_app_of_isLimit` concerns a fixed base and is not this morphism
base-change statement. No mismatch was found and no source, node, or Lean change was
needed. The module compiles cleanly with `scompile.py`; its only proof is the required
`sorry` for `Scheme.exists_isSeparated_overPullbackMap`.
