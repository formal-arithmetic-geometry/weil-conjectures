## Worker report

The module `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocallyFreeEvaluationBiduality`
states `SheafOfModules.locallyFreeEvaluationBiduality`. Its only postponed proof is
that theorem, whose docstring gives all five accepted DAG proof steps. The three
helper definitions contain real data: `bidualOverIso` composes the existing Hom
restriction identifications; `localBasisSection` evaluates the corresponding free
summand inclusion at 1; `localCoordinateFunctional` converts the corresponding
free coordinate projection to a section of the existing slice-Hom. They belong
to this node's canonical constructions, and do not introduce independent notions.
No new node, dependency repair, or statement correction is needed.

Hypotheses, individually:

- The site is small in the coefficient universe: `C : Type u`,
  `[Category.{u} C]`, `J : GrothendieckTopology C`. This is precisely the node's
  small-site convention, and keeps Hom and repeated duals in universe `u`.
- The arbitrary commutative ring sheaf is `R : Sheaf J CommRingCat.{u}`.
  Its underlying ring sheaf is `(sheafCompose J (forget₂ CommRingCat RingCat)).obj R`.
- The module sheaf `M` uses the dependency's transparent
  `CategoryTheory.ringedSiteModules.{u}` abbreviation for `SheafOfModules`.
- The small covering family is `{I : Type u}`, `U : I → C`,
  `hU : J.CoversTop U`. `CoversTop` is exactly membership of `Sieve.ofObjects U V`
  in `J V` for every V: the arrows whose domain admits a map to some `U i`.
- The varying nonnegative finite ranks are `r : I → ℕ`; `e` supplies each
  `M.over (U i) ≅ free (ULift.{u} (Fin (r i)))`. The harmless `ULift` places the
  finite indexing set in the module universe. No bound on `r` is imposed.
  The opposite orientation from free to M is obtained by `.symm`.

Conclusions, individually:

- `D_R(M)` is the recorded `SheafOfModules.homObj (R := R) M (unit _)`;
  its double iteration is the displayed bidual sheaf. These are slice-Hom,
  not duals of the single section modules.
- The map is the published `SheafOfModules.bidual (R := R) M`, whose type
  is a module-sheaf morphism. The first conjunct states exactly the evaluation
  formula for every section x over T, every `V : Over T`, and every local
  functional φ: evaluate φ at the identity of V on `M.val.map V.hom.op x`.
- Restriction of D is the public, existing `overHomObjIso M (unit _) T`.
  The new definition `bidualOverIso M T` applies that construction twice
  with coefficients `R.over T`; its type gives the D² identification. These
  are canonical maps, defined by relocalization, not arbitrary isomorphisms.
  The second conjunct identifies restricted evaluation with
  `bidual (R := R.over T) (M.over T)` through this identification for every T.
  The existing Hom restriction isomorphism sends local morphisms to themselves
  by the iterated-slice equivalence; hence iterated identifications use the
  same components. No extra geometric hypothesis is imposed for restriction.
- The third conjunct states `D²(f) δ_M = δ_N f` as the equality of the two
  categorical composites. N is completely arbitrary, and `homObjMap` twice
  is precisely contravariant precomposition twice. `bidual N` is the same
  canonical evaluation construction, with no local-freeness assumption on N.
- The last conjunct gives a global module-sheaf map s with both inverse
  equations `bidual M ≫ s = 𝟙 M` and `s ≫ bidual M = 𝟙 _`. This is the
  assertion that the specified evaluation is an isomorphism, with its inverse
  pinned down by these equations rather than chosen as an unrelated arrow.
- For every i and every chosen trivialization b of the given rank, it gives
  an actual module-sheaf isomorphism d from the restricted dual to the same
  free module. For every `V : Over (U i)` and every j, the coordinate
  `freeSectionsLinearEquiv ... (d.hom.val.app ... φ) j` is
  `φ(localBasisSection b j restricted to V)`, exactly the dual-basis formula.
- For that same arbitrary b and every further slice V, the component of s
  is the finite sum of `η(e_j^* restricted to V)` times `e_j restricted to V`.
  The coordinate functional is `localCoordinateFunctional b j`, explicitly
  the morphism `b.hom ≫ freeπ j`, not a functional chosen by an existence proof.
- The formulas hold at every V, and d and s are module-sheaf maps, so their
  components commute with every further restriction. Thus both the coordinate
  isomorphism and the inverse formula have the requested restriction compatibility.
- There is no global rank bound, point of the site, global finite-free retract,
  nonzero-ring hypothesis, or positivity hypothesis on the ranks.

Dependency declarations read and used:

- `def-weil-size-convention`: metatheoretic convention record; rendered by the
  explicit universe `u` and small site, coefficient and module universe choices.
- `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, transparently Mathlib's `SheafOfModules`.
  The full abbreviation and Mathlib's object and morphism structures were read.
- `def-pur-sheaf-hom`:
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
  `SheafOfModules.homObj`, `homObjMap`, `homFunctor`. The intrinsic
  ring-sheaf interface is usable here; the fixed-ring `ihom` alternative in
  that record is unnecessary.
- `def-pur-localized-ringed-site`:
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor`, `over`, `Hom.over`, `overMap`,
  `overFunctorMap`; `J.over` and `Sheaf.over` in `Mathlib.CategoryTheory.Sites.Over`.
  These declarations and their sectionwise signatures/docstrings were read.
- Proof leaf `lem-sfb-sheaf-cover-local-isomorphism`:
  `Mathlib.CategoryTheory.Sites.LocalProperties`,
  `CategoryTheory.Sheaf.isIso_of_coversTop`, imported as a proof dependency.

Other existing constructions read and reused: `SheafOfModules.bidual`,
`bidual_naturality`, `toRestrictOverHom` in the upstream `Sheaf.Bidual` module;
`overHomObjIso` in upstream `Sheaf.InternalHomOver` and its underlying
`PresheafOfModules.restrictOverHomObjIso`; `freeπ`, `freeSectionsLinearEquiv`
and `ιFree` in the upstream/Mathlib free-module files. The existing
`isIso_bidual` alone does not assert the local dual coordinates or inverse
formula, so attaching only that theorem would lose clauses.

The small-site sheafification instances are derived from Mathlib's existing
`Mathlib.CategoryTheory.Sites.LeftExact` and
`Mathlib.Algebra.Category.Grp.FilteredColimits`; no new hypotheses or local
instances have been introduced merely to use the free sheaf API.

Sources opened: current `literature/blueprint/latest/blueprint/` unit proof
`sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/lem-sf-hom-finite-projective.proof.md`
(first sentence: finite-free bidual identity; last: locality and restriction);
`literature/stacks-project/sites-modules.tex`, internal-Hom restriction lemma
at 3775ff (Tag 0E8H); `literature/stacks-project/sites.tex`, glue-maps lemma
at 5638ff (Tag 04TQ).

Edge cases checked before statement construction:

- Rank zero: `ULift (Fin 0)` is empty, the free sheaf is the zero sheaf, and
  the inverse formula is the empty sum. No basis index or distinguished element
  is required.
- Rank one: the formula is eta(e*) times e, giving the ordinary rank-one inverse.
- Zero coefficient rings are allowed; no faithfulness or rank invariance is used.
- Different finite ranks on unrelated or overlapping charts are allowed. Only
  the chosen trivializations impose their necessary compatibility.
- An empty covering family is allowed whenever `CoversTop` holds (a degenerate
  topology, or an empty site); then the sheaf conditions force the corresponding
  zero/unique module situation. No `Nonempty I` binder was added.
- An empty site has no section or slice tests, and the categorical inverse
  assertion remains valid in its unique module category.
- N in naturality may be zero, infinitely generated, or not locally free.
- No products in the site are required; all further restrictions use slice objects.

Duplicate searches (all dated 2026-10-24):

- `msearch.py ... leansearch "Finite locally free module sheaf has dual basis and
  canonical bidual isomorphism"`: returned `Module.Basis.dualBasis`,
  `dualBasis_equivFun`, `Module.IsReflexive.of_finite_of_free` and other ordinary
  module results. They do not state the ringed-site slice-Hom result.
- `msearch.py ... leanfinder "Locally finite free sheaf of modules evaluation
  double internal Hom is an isomorphism"`: returned free-sheaf universal
  properties (`ιFree_mapFree_inv`, `freeHomEquiv`, and naturality lemmas),
  not this evaluation/restriction/dual-basis/inverse package.
- `msearch.py ... loogle "SheafOfModules.bidual, SheafOfModules.homObj"`:
  unknown identifier `SheafOfModules.bidual` in the Loogle index. This is
  unavailable evidence, not evidence of absence.
- `msearch.py ... grep "bidual|overHomObjIso|freeSectionsLinearEquiv"
  Algebra/Category/ModuleCat`: zero Mathlib hits.
- `rg` of `lean/WeilConjectures` for bidual/Hom found the upstream canonical
  map, its naturality and IsIso theorem, and the restriction construction, all
  read in full. Search for this item's id in that root returned no match.
- `rg` of `lean/Sheaf` for bidual/Hom found, among others,
  `Sheaf.Paper.HomFiniteProjective`: it is a finite-projective ordinary/derived
  comparison package, and does not supply these local-basis formulas.
  The current node's accepted stage-1 split also distinguishes these results.
- `rg` of Mathlib, `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for `bidualOverIso`, `localBasisSection`,
  `localCoordinateFunctional`, `locallyFreeEvaluationBiduality`: no existing
  declaration with any delivered name.

No `STATEMENT-DISPUTED` issue or node fault was found. The node is unchanged
outside `lean`.

Validation: every compiler invocation used the prescribed `scompile.py` wrapper
with the 60-second per-file limit. Initial elaboration failures were repaired
by explicit coefficient arguments and the standard small-site sheafification
imports. Line-length warnings were shortened. The final clean compile and
server preflight results are recorded below after validation.

## Second reading by Q86

A separate reread by this same worker (the dispatcher explicitly prohibits
starting other agents), with the node and delivered module open. The delivery
is submitted for the maintainer's independent review; this is not represented
as an independent second worker review.

I matched the site/ring/module/family/rank/trivialization binders to the first
paragraph. I checked the evaluation formula uses a functional over V, not just
over T, and that the restriction equation uses the double-dual identification
with `R.over T`. I checked the naturality quantifier allows arbitrary N. I
checked the existential inverse has both categorical inverse equations, and
that the dual coordinate and inverse formulas both quantify every further
slice and every alternative chosen basis b of rank r_i, not only the input e.
The basis helper uses `e.inv` for the basis inclusion, while the coordinate
helper uses `e.hom` for the projection, so the orientations match. The sum
uses the restricted dual functional as eta's input and the restricted basis
vector as the summand. The compatibility requirement is supplied by module-
sheaf morphisms d and s and formulas at every slice. Rank zero, zero rings,
empty covers, and varying ranks remain included. No mismatch requiring a node
change was found in this second pass.

Final validation results: `scompile.py` returned exit 0 with no diagnostics in
both sandbox module mode (7.1 s) and the actual library module mode (9.3 s).
`deliver2.py Q86 lem-sf-locally-free-sheaf-evaluation-biduality --no-push`
returned `OK (dry run)`, confirming that the commit passes server preflight
and compiles; no source or DAG correction was needed for the dry run.
