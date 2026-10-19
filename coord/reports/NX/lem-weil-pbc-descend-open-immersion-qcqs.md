## Worker report

The module `lean/Sheaf/AlgebraicGeometry/OpenImmersionInverseLimitDescent.lean`
states `AlgebraicGeometry.IsOpenImmersion.eventually_of_inverseLimit` with a single
`sorry` proof. No definitions, dependency modules, new nodes, or statement corrections
were needed. The item node is changed only in `lean`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A nonempty directed set is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. A preorder is the Stacks directed-set convention.
- The inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`. Opposite arrows give the transitions
  from later to earlier indices. The same universe `u` is used for indices and schemes,
  following the shared limit convention; there is no smaller independent test universe.
- Every base stage is quasi-compact and quasi-separated: the two families
  `[∀ i : Iᵒᵖ, CompactSpace (D.obj i)]` and
  `[∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]` retain the node's all-stages hypotheses.
- Affine transitions are `[∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]`.
- The limit and its projections are `c : Cone D`, `hc : IsLimit c`, and `c.π.app`.
  A supplied limiting cone expresses exactly a choice of the limit whose existence
  is given by the recorded limit dependency; no particular construction is imposed.
- The chosen stage is `(i₀ : I)`.
- The two schemes over that stage are `X₀ Y₀ : Over (D.obj (op i₀))`. Their underlying
  schemes have the four explicit compactness/quasi-separatedness instances. These
  are qcqs schemes, as in Situation 081D; no affine or finite-type structure-map
  hypotheses are imposed.
- The morphism over that stage is `f₀ : X₀ ⟶ Y₀`, with local finite presentation
  expressed by `[LocallyOfFinitePresentation f₀.left]`. The `Over` morphism includes
  exactly compatibility with the two structural morphisms.
- The limit base change is `((Over.pullback (c.π.app (op i₀))).map f₀).left`;
  `hf : IsOpenImmersion ...` is precisely the assumption about `f`.
- The conclusion chooses `∃ (i : I) (hi : i₀ ≤ i)` and then quantifies over every
  `(j : I) (hij : i ≤ j)`. Its morphism is
  `((Over.pullback (D.map (homOfLE (hi.trans hij)).op)).map f₀).left`, namely `f_j`,
  and it is required to be an `IsOpenImmersion`.
- The last sentence, no affineness of either scheme assumed, is respected:
  neither `IsAffine X₀.left` nor `IsAffine Y₀.left` occurs.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and its morphisms.
- `def-weil-pbc-scheme-conventions`: this is a convention node with null declaration,
  not a new notion. Quasi-compact and quasi-separated schemes are `CompactSpace`
  and `QuasiSeparatedSpace`, as in the recorded descent dependencies and Mathlib's
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `pqf-def-affine-morphism`: its mathlib_match is `AlgebraicGeometry.IsAffineHom`
  in `Mathlib.AlgebraicGeometry.Morphisms.Affine`; the class tests affine-open preimages.
- `lem-weil-pbc-limit-affine-transition`: import
  `Sheaf.AlgebraicGeometry.LimitAffineTransition`, declaration
  `AlgebraicGeometry.exists_limit_affine_transition`. Its signature provides a cone
  with `IsLimit`; the present statement works with any such cone.
- `def-sbc-locally-finite-presentation`: mathlib_match
  `AlgebraicGeometry.LocallyOfFinitePresentation` in
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`. Its affine-open algebra
  condition is the recorded equivalent of the node's pointwise definition.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd` in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  `CategoryTheory.Over.pullback` in `Mathlib.CategoryTheory.Comma.Over.Pullback`
  uses these very pullbacks, not a duplicate construction: its object is
  `Over.mk (pullback.snd g.hom f)` and its map uses `pullback.lift`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` in
  `Mathlib.AlgebraicGeometry.OpenImmersion`.

Proof imports include the recorded `AlgebraicGeometry.Etale.exists_stage_of_inverseLimit`
(`Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`),
`AlgebraicGeometry.exists_mono_baseChange_stage`
(`Sheaf.AlgebraicGeometry.DescendMonomorphism`), and
`AlgebraicGeometry.IsOpenImmersion.of_etale_of_universallyInjective`
(`WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Gluing`).
The Mathlib proof-dependency imports provide `Scheme.isBasis_affineOpens`,
`LocallyOfFinitePresentation.finitePresentation_appLE`, `LocallyOfFiniteType`,
`Etale.instOfIsOpenImmersion`, `IsOpenImmersion.mono`,
`Etale.etale_isStableUnderBaseChange`, `UniversallyInjective`, and
`isOpenImmersion_stableUnderBaseChange`. The docstring gives all six DAG proof steps,
including both pullback identifications and the persistence at every later stage.

Source checked: local `literature/stacks-project/limits.tex`,
`situation-descent-property` (Situation 081D), lines 1739ff, and
`lemma-descend-open-immersion` (Tag 0EUU), lines 1991ff.
The source asserts one stage; open-immersion base-change stability supplies the
node's all-later assertion. The node assumes all base stages qcqs and these are
retained, even though the source only needs the chosen stage to be qcqs.

Edge cases checked before writing: an empty index type is explicitly excluded;
a one-element or constant system is allowed; `j = i` is included by reflexivity;
empty source, target, base stages, and empty limit are permitted. Neither field
nor characteristic nor nonemptiness of any scheme is assumed. Arbitrary qcqs
nonaffine sources and targets remain allowed. Preorder equality has no effect on
transition choices since its hom types and the inequality proofs are subsingletons.
No `STATEMENT-DISPUTED` issue or node fault was found.

Searches for a matching statement (all via the required tools/read-only sources):

- `msearch.py ... leanfinder "Open immersions descend to a stage of inverse limits
  of qcqs schemes with affine transition maps"`: eight hits, including affine-open
  descent, locally-finite-type map comparison, and eventual quasi-affineness;
  none is open-immersion descent of a morphism.
- `msearch.py ... loogle '"IsOpenImmersion", "IsLimit"'`: two hits on the
  limiting property of pullback cones in locally ringed/presheafed spaces;
  neither is the statement here.
- `msearch.py ... grep 'exists.*[Ii]sOpenImmersion|descend.*[Oo]penImmersion'
  AlgebraicGeometry`: three hits in LocalIso and FlatDescent, concerning local
  isomorphisms and fpqc descent, not inverse-limit descent.
- `rg` over `lean/Sheaf`, upstream `WeilConjectures`, and
  `dag/lean_names_upstream.json` for descent/open-immersion/limit patterns and
  `eventually_of_inverseLimit`: no matching declaration. Project fpqc descent
  is a different statement. `grep -rn` for the exact node id in upstream
  `WeilConjectures` returned no hits. The planned full declaration name is unused.

Validation: `scompile.py NX lem-weil-pbc-descend-open-immersion-qcqs` on the delivered
module passed with no errors or warnings (1.4 seconds, nice 19, two threads,
60-second per-file limit). The final dry run result is recorded below.


## Second reading by NX

I independently read the sandbox module and node, the seven statement-dependency
nodes and their recorded declarations, the proof-dependency signatures, and Stacks
`limits.tex`, Situation `situation-descent-property` (081D, lines 1739ff) and
`lemma-descend-open-immersion` (0EUU, lines 1991ff). The source assumes qcqs
S₀, X₀, Y₀ throughout and local finite presentation of f₀ in the lemma.
The node additionally specifies qcqs at every base stage and the all-later
conclusion; Lean retains the former, and base-change stability supplies the latter.
There is no statement correction and no new node or dependency module to review.

Object, hypothesis, and conclusion checklist (all verdicts: exact):

- Nonempty directed set I: `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. Thin preorder arrows give the same
  transition data as the source directed-set convention.
- Inverse system of schemes: `(D : Iᵒᵖ ⥤ Scheme.{u})` uses the recorded
  `AlgebraicGeometry.Scheme`; `Scheme.Hom` is a locally ringed space morphism.
- Affine transitions: `[∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]`.
  The recorded Mathlib class requires affine preimages of affine opens, exactly
  the dependency node's notion, without finite-type assumptions.
- Each Sᵢ qcqs: `[∀ i : Iᵒᵖ, CompactSpace (D.obj i)]` and
  `[∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]`. These are properties of the
  underlying schemes, not an extra relative finiteness condition.
- Limit S and projections: `(c : Cone D) (hc : IsLimit c)` and `c.π.app`.
  `exists_limit_affine_transition` really supplies such a limiting cone; the
  theorem permits every choice of it and imposes no additional cone condition.
- Initial index: `(i₀ : I)`.
- X₀ and Y₀ over Sᵢ₀: `(X₀ Y₀ : Over (D.obj (op i₀)))`. The four explicit
  `CompactSpace` and `QuasiSeparatedSpace` instances are precisely their qcqs
  assumptions. No affineness of either object or its structural map is required.
- Sᵢ₀-morphism: `(f₀ : X₀ ⟶ Y₀)` includes its structural-map compatibility.
- Local finite presentation: `[LocallyOfFinitePresentation f₀.left]` is on
  f₀ itself. Its Mathlib field tests finite presentation on affine pairs,
  equivalent to the dependency's pointwise formulation, not formal smoothness
  or a finite-presentation assumption on X₀ or Y₀ over Sᵢ₀.
- Base change f to the limit: `((Over.pullback (c.π.app (op i₀))).map f₀).left`.
  I opened `Over.pullback`: its objects are `Over.mk (pullback.snd g.hom f)`
  and its maps are the induced `pullback.lift`, so this uses the recorded fibre
  product and gives the actual base-changed morphism.
- Open-immersion hypothesis: `hf : IsOpenImmersion` of that morphism. The
  recorded Mathlib abbreviation uses the locally ringed space open immersion.
- Eventual stage with its comparison to i₀: `∃ (i : I) (hi : i₀ ≤ i)`.
- Every later stage, not just a single stage: `∀ (j : I) (hij : i ≤ j)`.
- Its open immersion fⱼ: `IsOpenImmersion
  (((Over.pullback (D.map (homOfLE (hi.trans hij)).op)).map f₀).left)`.
  The arrow is Sⱼ → Sᵢ₀, so this is exactly the stated base change of f₀.
- The explicit no-affineness clause is respected: no `IsAffine` assumption
  occurs on either X₀ or Y₀.

Dependency check: `LimitAffineTransition`, `EtaleInverseLimitDescent`, and
`DescendMonomorphism` were opened, including their actual theorem signatures.
The latter two apply to the same Over morphism and cone, require qcqs only at
Sᵢ₀, and require respectively local finite presentation and local finite type.
All are supplied by the present hypotheses and the documented finite-generation
step. I also opened upstream `IsOpenImmersion.of_etale_of_universallyInjective`:
it takes just `[Etale g] [UniversallyInjective g]`. No missing definition or
unusable dependency forces an additional module. Mathlib's
`quasiSeparatedSpace_iff_quasiSeparated` and `quasiCompact_iff_compactSpace`
confirm the qcqs encodings against the scheme-conventions node.

Edge cases: empty I is excluded by the node and explicitly by Lean (also by
having i₀). Singleton systems, constant systems, i = i₀, and j = i are allowed.
Empty schemes at any stage and an empty limit, source, or target are allowed;
no points or nonzero coordinate ring are assumed. Zero rings are therefore
covered. There is no n, characteristic restriction, base field, Noetherian
assumption, or separatedness assumption. The single arbitrary universe u for
indices and schemes follows the shared limit convention; any set-sized diagram
and its objects can be placed in a common universe. There is no independently
smaller universe of test schemes making a hypothesis vacuous.

Independent duplicate searches (different phrases from the author's):

- LeanFinder via msearch: "A locally finitely presented map becomes an open
  immersion at a sufficiently large index if it is so over the inverse limit".
  Eight results: finite presentation of an open immersion, open immersions in
  gluing/colimits, and source-local recognition; no inverse-limit descent result.
- Loogle via msearch: `"IsOpenImmersion", "IsCofiltered"`: zero hits.
- LeanSearch via msearch: "Being an open immersion descends through an inverse
  system with affine transition morphisms": unavailable (Internal Server Error);
  this supplies no negative mathematical evidence.
- `rg -i` on Mathlib AlgebraicGeometry, upstream WeilConjectures, and project
  lean/Sheaf for open-immersion plus inverse/descent/eventual phrases found fpqc
  descent and gluing or unrelated restriction results, no matching statement.
  Exact declaration-name and node-id searches in the upstream names map and
  upstream source found no hits. Thus there is no existing declaration to reuse.

H5/H6/H8/H9: the delivery introduces no definitions and proves nothing: the
single theorem has `by sorry`. Its module and declaration docstrings cite 0EUU
and the blueprint id. The declaration docstring follows all six proof steps,
including finite type from finite presentation, common upper bound, pullback
identifications, radicial recognition, and all-later persistence. Imports cover
the recorded statement and proof dependencies. All lines are at most 100
characters; all variables and the sole universe are explicitly bound. I checked
programmatically that `lean.statement` is verbatim the signature in the module.

Mismatches found: none. No Lean or node change was needed; only this independent
second-reading report was appended. Server validation with the mandated
`scompile.py` passed cleanly: 1.4 seconds, nice 19, two threads, 60 seconds per
file. The initial invocation used the repository working directory and could
not find the sandbox-relative path; rerunning from the sandbox fixed the path
without any compiler or tool modification.
