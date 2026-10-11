## Worker report

Module `Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent` states
`AlgebraicGeometry.Etale.exists_stage_of_inverseLimit` with one sorry-only proof.
No definitions, dependency modules, new nodes, or statement corrections are needed.

Source read: [Stacks 07RP](https://stacks.math.columbia.edu/tag/07RP), Lemma 32.8.10,
and [Stacks 081D](https://stacks.math.columbia.edu/tag/081D), Situation 32.8.1.
The local Stacks source is absent on this machine, so these official pages were opened.
They give exactly the node's assumptions and conclusion. The docstring records all six
steps of the node's natural-language proof, with the dependency ids each step uses.

Hypothesis and clause correspondence:

- Directed set: `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]`.
  A preorder suffices; antisymmetry is not used or imposed.
- Inverse system of schemes: `D : Iᵒᵖ ⥤ Scheme.{u}`. Functoriality supplies the
  identities and compatible transition maps. For `h : i₀ ≤ i`, the transition to
  the distinguished stage is `D.map (homOfLE h).op`.
- Affine transitions: `[∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]`.
- Limit S with its projections: `(c : Cone D) (hc : IsLimit c)`, with S = `c.pt`
  and projection to S₀ = `c.π.app (op i₀)`. This uses the cone notion of the recorded
  `exists_limit_affine_transition` statement, imported from its recorded module.
  The node assumes a limit, so its existence theorem need not be a premise or invoked.
- Distinguished element 0: `(i₀ : I)`; no least-element assumption is added.
  This binder already excludes empty I, exactly as “let 0 ∈ I” does.
- S₀ quasi-compact and quasi-separated: `[CompactSpace (D.obj (op i₀))]` and
  `[QuasiSeparatedSpace (D.obj (op i₀))]`.
- X₀ and Y₀ over S₀: `(X₀ Y₀ : Over (D.obj (op i₀)))`.
  Their structure morphisms are `X₀.hom` and `Y₀.hom`.
- X₀ and Y₀ quasi-compact and quasi-separated: the four separate instances
  `[CompactSpace X₀.left]`, `[QuasiSeparatedSpace X₀.left]`,
  `[CompactSpace Y₀.left]`, `[QuasiSeparatedSpace Y₀.left]`.
- Morphism over S₀: `(f₀ : X₀ ⟶ Y₀)`; `f₀.left` is the scheme morphism,
  and the over-category equation enforces compatibility with structure morphisms.
- Base changes Xᵢ, Yᵢ and fᵢ: `Over.pullback (D.map (homOfLE h).op)`
  sends the over-objects to the chosen fibre products, with projection to Sᵢ;
  its map on `f₀`, followed by `.left`, is exactly the induced scheme morphism.
- Base change X, Y and f to S: the same functor using `c.π.app (op i₀)`.
- f étale: `hf : Etale (((Over.pullback (c.π.app (op i₀))).map f₀).left)`.
- f₀ locally of finite presentation: `[LocallyOfFinitePresentation f₀.left]`.
- Conclusion: `∃ (i : I) (h : i₀ ≤ i), Etale
  (((Over.pullback (D.map (homOfLE h).op)).map f₀).left)`.
  This asserts an actual index at or above the distinguished stage with étale fᵢ.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; full structures and docstrings read.
- `pqf-def-affine-morphism`: `AlgebraicGeometry.IsAffineHom`,
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`.
- `lem-weil-pbc-limit-affine-transition`: `AlgebraicGeometry.exists_limit_affine_transition`,
  `Sheaf.AlgebraicGeometry.LimitAffineTransition`; full signature and docstring read.
  The theorem's explicit limiting-cone interface is reused rather than constructing a
  second inverse-limit notion.
- `def-weil-pbc-scheme-conventions`: a convention node, explicitly giving no new
  declaration; its Mathlib scheme compactness and quasi-separatedness are used.
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` was read for its scheme-space
  equivalences (`quasiSeparated_iff_quasiSeparatedSpace`, `quasiCompact_iff_compactSpace`).
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.lift`,
  `.map`, `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  Their full signatures/docstrings were read. `CategoryTheory.Over.pullback` in
  `Mathlib.CategoryTheory.Comma.Over.Pullback` builds its object and map using those
  exact chosen pullbacks and the universal lift; its full definition was read.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`; full class and docstring read.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`; full class/docstring read.

Edge cases checked before writing: empty I is incompatible with the specified i₀;
no additional nonemptiness assumption is imposed. A singleton index system is allowed.
Empty source, target or base schemes are allowed (no point or nonempty-space hypotheses).
No field, characteristic, finite-type, separated, or affine-stage assumption is added.
Only the distinguished schemes must be qcqs; later stages and the limit have no extra
qcqs premises. I and schemes share the universe as in the recorded limit dependency;
arbitrary larger systems can be represented by taking a common larger universe. There
is no quantification over test schemes in a smaller universe. IsLimit is the universal
property, and the base-change maps are constrained by Over.pullback, not arbitrary maps.

Searches executed using `/home/ubuntu/weil-launcher/msearch.py` (logged in searches.jsonl):

- leansearch: “Etale morphism descends to a finite stage of an inverse limit of schemes
  with affine transition maps”: unavailable, Internal Server Error; no verdict assigned.
- loogle: `AlgebraicGeometry.Etale, CategoryTheory.Limits.IsLimit`: zero hits.
- leanfinder: “Etaleness of a locally finitely presented scheme morphism descends from
  inverse limit to some finite stage”: eight hits, including IsEtale.of_comp,
  Algebra.Etale.finitePresentation, and étale-locus results, none this statement.
- grep: `07RP|descend.*etale|etale.*limit` in Mathlib/AlgebraicGeometry:
  two hits in LocalFlatDescent, about faithfully flat descent rather than limit descent.
- rg in WeilConjectures and lean/Sheaf for `descend.*[Ee]tale|[Ee]tale.*[Ll]imit`:
  related faithfully flat descent, ring-colimit descent, étale sheaf continuity and
  finite-étale lifting; none states the node. The quotient lemma
  `isFinite_and_etale_of_isColimit` in WeilConjectures/Mathlib/AlgebraicGeometry/ColimitsOver
  was read and concerns a finite monoid quotient, not inverse-limit descent.
- `grep -rn lem-weil-pbc-descend-etale` in WeilConjectures: no hits.
- Name/tag check for `exists_stage_of_inverseLimit|07RP|descend.*[Ee]tale` in Mathlib,
  WeilConjectures and lean/Sheaf: proposed name absent; only unrelated descent results.
  `dag/lean_names_upstream.json` was searched for descent/07RP as well.

Server compile via scompile.py: clean, exit code 0, 1.7 seconds; no warnings.
No statement dispute or node fault found.

## Second reading by J1

I independently opened the item node, its delivered Lean file, every statement-dependency
node, the recorded LimitAffineTransition module, and the Mathlib declarations listed below.
The local Stacks checkout is absent. I read the actual `limits.tex` source from
https://raw.githubusercontent.com/stacks/stacks-project/master/limits.tex at
`lemma-descend-etale` (07RP) and `situation-descent-property` (081D), and checked the
corresponding official tag pages. Situation 081D supplies precisely the qcqs assumptions
in the node; 07RP supplies the two hypotheses and the existential conclusion.

Object, hypothesis and conclusion checklist (each verdict is exact):

1. Directed index set I: `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]`.
   A preorder is the project's directed-set convention; no least element is assumed.
2. Inverse system of schemes S_i with compatible transition maps:
   `(D : Iᵒᵖ ⥤ Scheme.{u})`. The opposite preorder gives maps from larger indices to
   smaller ones and functoriality supplies identities and composition.
3. Every transition affine:
   `[∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]`.
   The class in Morphisms/Affine.lean is exactly affine inverse images of affine opens.
4. Limit S and its compatible projections: `(c : Cone D) (hc : IsLimit c)`;
   S is `c.pt` and its projection to S_0 is `c.π.app (op i₀)`.
   I opened `exists_limit_affine_transition`: it uses the same diagram/cone interface.
   Its theorem proves existence and affine projections; those consequences need not be
   repeated as extra premises. An arbitrary limiting cone is the limit the node specifies.
5. Distinguished stage 0 ∈ I: `(i₀ : I)`. This is an element, not an assumed bottom.
6. S_0 qcqs: `[CompactSpace (D.obj (op i₀))]` and
   `[QuasiSeparatedSpace (D.obj (op i₀))]`.
7. X_0 and Y_0 over S_0: `(X₀ Y₀ : Over (D.obj (op i₀)))`.
   Each has the specified scheme as `.left` and its structure morphism as `.hom`.
8. X_0 qcqs: `[CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]`.
9. Y_0 qcqs: `[CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]`.
   These are absolute scheme-space properties, not extra separatedness assumptions;
   I read `quasiSeparated_iff_quasiSeparatedSpace` and
   `quasiCompact_iff_compactSpace` in Morphisms/QuasiSeparated.lean.
10. Morphism f_0 over S_0: `(f₀ : X₀ ⟶ Y₀)`.
    Its underlying morphism is `.left`; the over-category condition is the required
    compatibility with the two structure maps.
11. X_i, Y_i and f_i for i ≥ 0: `Over.pullback (D.map (homOfLE h).op)`
    on the two objects and its `.map f₀`, respectively. I opened Over/Pullback.lean:
    its object is `Over.mk (pullback.snd g.hom q)`, with underlying scheme
    `pullback g.hom q`; its map is the universal `pullback.lift` of
    `pullback.fst ≫ f₀.left` and `pullback.snd`. Thus the maps are exactly
    f_0 × identity, with no arbitrary unconstrained base-change morphism.
12. X, Y and f over S: the same pullback functor at `c.π.app (op i₀)`.
13. f étale: `(hf : Etale (((Over.pullback (c.π.app (op i₀))).map f₀).left))`.
    I opened the recorded class Etale in Morphisms/Etale.lean; it imposes étale
    coordinate-ring maps on affine opens, the source notion.
14. f_0 locally of finite presentation: `[LocallyOfFinitePresentation f₀.left]`.
    I opened the recorded class in Morphisms/FinitePresentation.lean; no finite type,
    Noetherian or proper hypothesis is substituted or added.
15. Conclusion: `∃ (i : I) (h : i₀ ≤ i),
    Etale (((Over.pullback (D.map (homOfLE h).op)).map f₀).left)`.
    The witness index is quantified after all the input data and the limit hypothesis;
    its inequality gives exactly the required transition and étale base change.

I also opened `Scheme` and `Scheme.Hom` in Scheme.lean, and `pullback`, its two
projections and `pullback.lift` in Pullback/HasPullback.lean. These are the recorded
scheme and fibre-product dependencies, not private substitutes. The scheme-conventions
node explicitly fixes no declaration of its own. No new node or dependency module is
in this delivery; none is needed. There is no statement correction to check against citers.

Edge cases: an empty I has no distinguished i₀, exactly as in the source; a singleton I
is permitted and no strictly later index is required. Empty source, target or base schemes
are permitted. No nonempty point, nonzero ring, field, characteristic or dimension condition
is present. There is no numeric n to constrain. The universe u is bound, the index and
schemes have a common universe as in the recorded limit dependency, and any set-sized
system can be placed in a common larger universe. No smaller-universe test-object
quantification makes a hypothesis vacuous. None of the structural premises is hollow.

Independent searches used different wording from the worker and were logged by msearch.py:

- LeanFinder: “A morphism of quasi compact quasi separated schemes which becomes etale
  over a projective limit with affine bonding maps is etale after pullback to a sufficiently
  late stage”: eight results, all étale composition, base change or category declarations;
  none is inverse-limit descent.
- Loogle: `AlgebraicGeometry.Etale, CategoryTheory.Over.pullback`: no results.
- Mathlib grep: `etale.*(stage|inverse|limit)|((stage|inverse|limit).*etale)` in
  AlgebraicGeometry: only preservation of finite limits by the étale forgetful functor.
- LeanSearch: “Descent of etaleness for a locally finitely presented morphism along an
  inverse system of qcqs schemes with affine transition morphisms”: service unavailable
  (Internal Server Error); no mathematical verdict drawn from that failed search.
- Independent rg over WeilConjectures, repository lean/Sheaf and lean_names_upstream.json
  for étale combined with stage/inverse/limit, the proposed declaration and 07RP.
  I inspected the candidate modules FiniteEtaleLiftingLimitDescent and
  EtaleAlgebraFilteredColimitDescent: respectively a henselian lifting reduction and
  existence of an algebra model, neither this assertion about a given scheme morphism.
  I read `isFinite_and_etale_of_isColimit` in the upstream ColimitsOver module:
  it concerns a finite-monoid quotient, not the present directed inverse limit.
  No existing exact declaration or name collision was found.

H5/H6/H8/H9: there is no new definition, only one named theorem with proof `sorry`.
The module and declaration docstrings name 07RP, 081D and the correct blueprint id.
The theorem docstring carries all six node proof steps and their cited dependencies:
finite affine triples; ring colimits over base opens; tensor-product pieces and maps;
étaleness of the limit piece; descent of each ring map and persistence; a common stage
and locality on the source. Imports and namespace follow the project conventions,
all lines are within 100 characters, and all variables and the universe are bound.

No mathematical mismatch was found; the Lean source and node statement are preserved.
The lean.statement record already equals the literal multiline signature verbatim. The only substantive addition is this
independent second-reading report. Compilation and delivery preflight are recorded below.

Second-reader verification: scompile.py compiled the unchanged 71-line module in 1.7 s,
exit code 0, with no warnings. deliver2.py --no-push printed OK: the delivery passes
the stage-2 preflight and compiles.
