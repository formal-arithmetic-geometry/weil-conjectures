## Worker report

The module `Sheaf.AlgebraicGeometry.Modules.ModuleSkyscraperStalkAdjunction` states
`AlgebraicGeometry.Scheme.Modules.exists_moduleSkyscraperStalkAdjunction`, with one
`sorry` proof and no definitions. It reuses the landed concrete skyscraper and
stalk functors. Their already-landed definition nodes
`def-pc-ringed-module-skyscraper` and `def-pc-module-stalk-functor` are added to
`stmt_deps` under brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES). No new node,
dependency replacement, or statement correction is needed.

Source checked: Stacks Project [009A](https://stacks.math.columbia.edu/tag/009A),
case (4), and [009C](https://stacks.math.columbia.edu/tag/009C), module case.
The local `literature/stacks-project/sheaves.tex` is absent on this machine, so
these official pages were opened. They give skyscrapers as module direct images
from the stalk ring and the stated module adjunction, with proof omitted.
The docstring includes all four agent-written proof steps of the node.

Hypotheses and construction, clause by clause:

- `X : Scheme.{u}` and `x : X` render the scheme and chosen point; the structure
  sheaf is `X.sheaf`, and the ring is `X.presheaf.stalk x`. Passing
  `X.toRingedSpace` to the existing functors retains exactly this structure.
- `G : X.Modules` renders an arbitrary sheaf of O_X-modules. This is Mathlib's
  `SheafOfModules.{u} X.ringCatSheaf`, definitionally the source category of
  `RingedSpace.moduleStalkFunctor X.toRingedSpace x`.
- `A : ModuleCat.{u} (X.presheaf.stalk x)` renders an arbitrary stalk-ring module.
  Its module structure and abelian group are bundled; these impose no extra
  algebraic hypotheses. The universe matches Mathlib's scheme module category.
- `SheafOfModules.ringedModuleSkyscraperFunctor X.toRingedSpace x` uses precisely
  the prescribed skyscraper construction. Its object has sections
  `PLift (x ∈ U) → A`: evaluation at `⟨hx⟩` identifies these with A when x belongs
  to U; when x does not belong, the function space has a unique element and is
  the zero module. Restrictions precompose membership proofs, thus give the
  identity under these identifications if the smaller open contains x, and the
  zero map otherwise. The scalar action is through `X.presheaf.germ U x hx`.
  Its morphism map applies h pointwise, giving h on opens containing x and the
  zero map on all other opens. All of these data are read from the landed
  definition, not posited as hypotheses or privately copied.

Conclusions, clause by clause:

1. The functor's codomain is the category of sheaves of modules, so its objects
   already carry the sheaf condition. The explicit `.Additive` conjunct gives
   additivity. Functoriality on identities and composition is in the existing
   `ringedModuleSkyscraperFunctor` structure. The scalar and restriction rules
   above are its concrete definition.
2. `∃ adj : moduleStalkFunctor ... ⊣ ringedModuleSkyscraperFunctor ...` supplies
   for every G and A the equivalence `adj.homEquiv G A`. Mathlib orients it from
   stalk-linear maps to sheaf morphisms, so the node's Phi is its `.symm`.
   The first universal equation says exactly
   `Phi(φ)(germ s) = (φ.val.app (op U) s) ⟨hx⟩`, for every open containing x and
   section s. The result type of Phi is a ModuleCat morphism, hence linear;
   an `Equiv` is well-defined and bijective. The second universal equation
   specifies the inverse on every section of every open containing x as
   `ψ (germ s)`. On opens missing x there is only one possible section-map
   into the zero module, so the inverse there is necessarily the zero map.
3. Naturality in both variables is part of an `Adjunction`, with the exact
   node equations supplied by
   `CategoryTheory.Adjunction.homEquiv_naturality_left_symm` and
   `CategoryTheory.Adjunction.homEquiv_naturality_right_symm` in
   `Mathlib.CategoryTheory.Adjunction.Basic`. The first identifies
   `Phi(g ≫ φ)` with `moduleStalkFunctor.map g ≫ Phi(φ)`, and the second
   identifies `Phi(φ ≫ ringedModuleSkyscraperFunctor.map h)` with `Phi(φ) ≫ h`.
   The stalk functor's map is the stalk-linear map g_x, and the skyscraper
   functor's map is i_*h. Thus the adjunction is the specified natural
   equivalence, rather than an unspecified bijection.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (imported through Modules.Sheaf).
- `def-weil-sheaf-of-modules-category`: `SheafOfModules`,
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`, and its specialization
  `AlgebraicGeometry.Scheme.Modules` in `Mathlib.AlgebraicGeometry.Modules.Sheaf`.
- `def-weil-pbc-module-stalk`: `TopCat.Presheaf.stalk`, `.germ`,
  `PresheafOfModules`' stalk module instances and `.germ_ringCat_smul`/`.germ_smul`
  in `Mathlib.Algebra.Category.ModuleCat.Stalk`. The landed moduleStalkFunctor
  uses these same definitions and its map is the abelian stalk map packaged
  as a linear morphism.
- `def-pc-module-stalk-functor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor` and `.moduleStalkMap`,
  `Sheaf.Algebra.Homology.ModuleStalkFunctor`, imported by the skyscraper module.
- `def-pc-ringed-module-skyscraper`:
  `SheafOfModules.ringedModuleSkyscraperFunctor`, its object and map data,
  and `.ringedModuleSkyscraperFunctor_additive`,
  `Sheaf.Topology.RingedModuleSkyscraper`.

Edge cases checked before writing: the empty scheme has no chosen point, so the
statement is vacuous as it should be; the empty open and any open missing x
have a unique zero section; the zero value module is permitted; empty covers
of the empty open glue uniquely; no T1/closed-point hypothesis is needed,
including for generic points. There are no finiteness, reducedness, field,
characteristic, or quasi-coherence assumptions. All variables and the universe
are explicitly bound. No statement fault or STATEMENT-DISPUTED issue found.

Searches on 2026-10-11:

- msearch.py LeanFinder: `skyscraper sheaf of modules over structure sheaf right
  adjoint to module stalk functor`. Eight results: fixed-category stalk/skyscraper
  adjunctions in Mathlib.Topology.Sheaves.Skyscraper and an unrelated right adjoint
  to the module presheaf forgetful functor; no matching module adjunction.
- msearch.py Loogle: `skyscraperHomEquiv, SheafOfModules`. Zero results;
  `skyscraperHomEquiv` unknown in the search service's Mathlib index.
- msearch.py grep: `skyscraper` in `Algebra/Category/ModuleCat`. Zero results.
- msearch.py LeanSearch: `skyscraper sheaf module stalk adjunction`. Service
  unavailable (Internal Server Error); no mathematical verdict inferred.
- Local rg: `skyscraper|stalkFunctor|def-weil-pbc-module-stalk` in WeilConjectures
  and lean/Sheaf. Found the two landed definitions reused here. The source's
  `WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk` has
  `Scheme.Modules.skyscraperHomEquiv`, which was read in full, together with
  skyscraper section/action/restriction data, `toSkyscraper`, and stalk maps.
  This is an objectwise equivalence (oriented opposite to Phi), with the left
  precomposition law `comp_toSkyscraper`. It does not declare the additive
  skyscraper functor and adjunction with naturality in both variables as the
  complete node states; no duplicate definition or equivalence is introduced.
- Local rg: `lem-weil-pbc-module-skyscraper-stalk-adjunction` in WeilConjectures:
  no result. `skyscraper.*[Aa]djunction|[Aa]djunction.*[Ss]kyscraper` in lean/Sheaf:
  no existing adjunction statement.
- Local rg: `exists_moduleSkyscraperStalkAdjunction` in Mathlib, WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json: no pre-existing declaration.

Validation: `scompile.py G1 lem-weil-pbc-module-skyscraper-stalk-adjunction
<module>` compiled cleanly on the server in 1.7 seconds, exit code 0, no warnings.

## Second reading by G1

Independent reading on 2026-10-11. I opened the sandbox node and Lean file,
all five statement-dependency nodes, the two landed functor modules, and the
Mathlib declarations for Scheme, Scheme.Modules, SheafOfModules and the module
stalk action. There are no new nodes, dependency replacements or statement
corrections in this delivery.

Source reading: local sheaves.tex is absent. I read the actual Stacks TeX from
https://raw.githubusercontent.com/stacks/stacks-project/master/sheaves.tex,
section `section-skyscraper-sheaves`, especially
`definition-skyscraper-sheaf` (4) and `lemma-stalk-skyscraper-adjoint`, and
checked the official [009A](https://stacks.math.columbia.edu/tag/009A),
[009C](https://stacks.math.columbia.edu/tag/009C), and surrounding
[0099](https://stacks.math.columbia.edu/tag/0099) pages. The section assumes a
topological space, and its module case a ringed space and a stalk-ring module;
there is no closed-point, separation, finiteness, field or characteristic
hypothesis. The node deliberately specializes this to schemes. The source's
adjunction has stalk as left adjoint, as does the Lean.

My object/hypothesis/conclusion checklist, matched to Lean:

1. Scheme X with structure sheaf O_X: `(X : Scheme.{u})`, `X.sheaf`,
   `X.presheaf`, and `X.toRingedSpace`. Mathlib Scheme extends LocallyRingedSpace
   with local affine charts; passing to RingedSpace keeps its structure sheaf.
   Verdict: exact, no additional hypothesis.
2. Point x and its local ring with germ maps: `(x : X)`,
   `X.presheaf.stalk x` and `X.presheaf.germ`. The module-stalk dependency uses
   Mathlib's actual colimit stalk and its germ scalar action, not a residue
   field or sections over a chosen neighbourhood. Verdict: exact.
3. Arbitrary O_X-module G and its stalk G_x: `(G : X.Modules)` and
   `(RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G`. Mathlib's
   `Scheme.Modules` is `SheafOfModules.{u} X.ringCatSheaf`. The landed functor
   has precisely that source after specializing to X.toRingedSpace; its object
   is the abelian presheaf stalk with the Mathlib stalk-ring module instance.
   Its map is the ordinary induced stalk map, packaged linearly using
   `stalkMap_linear`. Verdict: exact; no quasi-coherence assumption.
4. Arbitrary O_{X,x}-module A and linear h: `ModuleCat.{u}
   (X.presheaf.stalk x)` and its morphisms. Bundling adds only the stated
   abelian group and module structure. Verdict: exact.
5. Prescribed skyscraper sections, restrictions, scalar action and maps:
   `SheafOfModules.ringedModuleSkyscraperFunctor X.toRingedSpace x`.
   I read its full definition: sections are `PLift (x ∈ U) → A`, restrictions
   precompose the inclusion of membership proofs, scalars act through
   `Module.compHom A (X.presheaf.germ U x hx).hom`, and maps act pointwise by h.
   Evaluation at hx identifies sections with A on opens containing x;
   otherwise the function space is the zero module. Thus all stipulated
   identity/zero restrictions and h/zero components are present.
   Verdict: exact through the recorded dependency, no private definition.
6. Conclusion (1), sheaf condition and additive functor: the functor's target
   is SheafOfModules, whose `isSheaf` field gives the sheaf condition, and its
   functor fields give identity/composition. The theorem's first conjunct is
   this functor's `.Additive`. Although the landed definition already has
   additivity, retaining it here states the node's entire conclusion.
   Verdict: exact.
7. Conclusion (2), well-defined linear bijection Phi: `∃ adj :
   moduleStalkFunctor ... ⊣ ringedModuleSkyscraperFunctor ...` supplies
   `(adj.homEquiv G A).symm`, from sheaf morphisms to ModuleCat morphisms.
   `Equiv` includes both inverse laws; the codomain consists of linear maps.
   The first universally quantified equation specifies its value on every
   germ as `(φ.val.app (op U) s) ⟨hx⟩`. Verdict: exact, with correct orientation.
8. Conclusion (2), the inverse Psi: the second universal equation specifies
   `adj.homEquiv G A ψ` on each section of every open containing x as
   `ψ (TopCat.Presheaf.germ ... s)`. On opens missing x its target is the
   function module on an empty type, so every map into it is necessarily the
   unique zero map; this is determined by the concrete definition rather
   than omitted from the assertion. Verdict: exact.
9. Conclusion (3), naturality in G: I read
   `Adjunction.homEquiv_naturality_left_symm` in Mathlib, whose equation is
   `(adj.homEquiv G' A).symm (g ≫ φ) = F.map g ≫
   (adj.homEquiv G A).symm φ`. Here F is exactly the landed stalk functor.
   This is Phi(phi composed with g) = Phi(phi) composed with g_x.
   Verdict: exact, encoded by Adjunction rather than extra conjuncts.
10. Conclusion (3), naturality in A: Mathlib's
    `Adjunction.homEquiv_naturality_right_symm` gives
    `(adj.homEquiv G A').symm (φ ≫ K.map h) =
    (adj.homEquiv G A).symm φ ≫ h`, where K is the concrete skyscraper functor.
    This is the node's second naturality equation. The same adjunction works
    for every G and A: the existential is outside both universal formulas.
    Verdict: exact, with the required quantifier order.

Edge cases: no point can be supplied for the empty scheme, as in the node.
For the empty open and any open missing x the section function has empty
source and a unique value; thus zero targets and empty-cover gluing are
included. The zero module and zero sheaf are allowed. Generic and nonclosed
points are allowed; no T1 instance occurs. No n or index set is a parameter;
there is no degree-zero or empty-index exclusion. No characteristic or
nontriviality instance is assumed. `universe u` is arbitrary and matches the
recorded Scheme.Modules and both landed functor universes. A larger value
universe can be accommodated by taking a common ambient universe for the
scheme and its modules; no fixed small universe or independent test-object
universe appears. All binders and the sole universe are explicit.

Independent searches (different wording from the worker):

- msearch LeanFinder: `linear maps from module sheaves to point supported
  modules correspond naturally to linear maps from stalks`. Eight results,
  all ModuleCat.Tilde stalk/fiber constructions; no matching adjunction.
- msearch Loogle: `"skyscraper", "stalk"`. Twelve hits in
  Mathlib.Topology.Sheaves.Skyscraper. I checked the displayed signatures:
  these are for fixed C-valued sheaves, not O_X-modules with stalk-ring values.
- msearch LeanSearch: `ringed space modules stalk right adjoint point direct
  image`. Service returned Internal Server Error; recorded as unavailable,
  with no mathematical verdict inferred.
- Independent rg for `skyscraper|point.?support` in Mathlib ModuleCat and
  AlgebraicGeometry found no module adjunction. Searching project Lean and
  WeilConjectures for skyscraper/adjunction in either order, and
  `skyscraperHomEquiv`, found the source FlatPullbackStalk module and the two
  reused landed definitions, not an existing complete statement. The site
  skyscraper declarations in the source concern fixed coefficient categories.
- I opened FlatPullbackStalk.lean lines 80-178 and 275-326: its
  `Scheme.Modules.skyscraperHomEquiv` is an objectwise linear-map equivalence
  with concrete germ formulas, and `comp_toSkyscraper` gives precomposition.
  Neither declares the additive skyscraper functor or the adjunction natural
  in both variables required by the whole node. The delivered module adds no
  second skyscraper definition or separately defined equivalence.

No mismatch found; no Lean or node change was necessary. The only change in
this second reading is this independent review section (and search log).
The module contains one theorem with `by sorry`, no definitions, and its
module/declaration docstrings give the source, blueprint id and all four
natural-language proof steps. Imports are used by the scheme module type,
adjunction and concrete skyscraper respectively; namespace/header follow
the project's conventions. The node's lean.statement matches the file's
signature verbatim, excluding `:= by`. Server compilation and delivery
preflight are run again for this second reading below.

Second-reading validation: scompile.py compiled the unchanged module in 1.7 s,
exit code 0, no warnings. An exact string comparison confirmed lean.statement
is the file signature, and every Lean line is at most 100 characters.
`deliver2.py G1 lem-weil-pbc-module-skyscraper-stalk-adjunction --no-push`
printed OK: preflight and compilation passed.
