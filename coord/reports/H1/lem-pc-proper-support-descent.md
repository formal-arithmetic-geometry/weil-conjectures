## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ProperSupportDescent.lean` states
`AlgebraicGeometry.exists_hasSupportProperOver_baseChange_of_isLimit`, with its sole
proof `sorry`. It defines no new notion and makes no statement correction.

Hypothesis and conclusion correspondence:

- The directed set is `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]`.
  The chosen stage `(i : I)` already supplies nonemptiness; no extra instance is required.
- The rings and their compatible transition maps are `R : I ⥤ CommRingCat.{u}`.
  The inverse system is `R.op ⋙ Scheme.Spec`; its objects are `Spec (R.obj k)`
  and its maps are `Spec.map (R.map (homOfLE hij))` in the reverse direction.
  Thus every base is affine (and consequently quasi-compact and quasi-separated),
  and every transition is affine. These conditions follow from this exact Spec
  presentation and are not replaced by additional universal or vacuous hypotheses.
- Noetherianity of every stage ring is `[∀ k : I, IsNoetherianRing (R.obj k)]`.
- The inverse limit is the cone `c : Cone (R.op ⋙ Scheme.Spec)` with
  `hc : IsLimit c`. Its base scheme is `c.pt`; `[IsAffine c.pt]` renders the
  node's `S = Spec(R)`. Naming its coordinate ring separately would not impose
  an additional condition: an affine scheme is canonically isomorphic to the
  spectrum of its ring of global sections. Cone projections specify the base maps.
- `Xi : Scheme.{u}` and `f : Xi ⟶ Spec (R.obj i)` are the finitely presented
  stage scheme and its structure morphism. Finite presentation means precisely
  `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`,
  as specified by the morphism-convention dependency.
- `Fi : Xi.Modules` with `[Fi.IsFinitePresentation]` is the finitely presented
  structure-sheaf module. Mathlib defines this by local presentations with finite
  generators and relations and supplies both quasi-coherence and finite type.
  Neither is an extra assumption in this statement.
- `X = Xi ×_{S_i} S` is `pullback f (c.π.app (op i))`. Its map to `S` is
  `pullback.snd`; its map to `Xi` is `pullback.fst`.
- The module `F` is
  `(Scheme.Modules.tensorPullback (pullback.fst f (c.π.app (op i)))).obj Fi`.
  This is the tensor module pullback required by `def-pc-base-change`, not the
  differently defined Mathlib functor named `Scheme.Modules.pullback`.
- The hypothesis `hF` is `Scheme.Modules.HasSupportProperOver` for exactly that
  module and its structure map. It includes closedness of the nonzero-stalk locus
  and properness of its reduced induced closed subscheme.
- `∃ (j : I) (hij : i ≤ j)` gives the required later stage; equality is allowed.
- At that stage, `pullback f (Spec.map (R.map (homOfLE hij)))` is exactly `X_j`.
  The conclusion applies the same proper-support definition to the tensor
  pullback of the original `Fi` along its first projection, over its second
  projection to `Spec (R.obj j)`. It neither asserts properness of all of `X_j`
  nor imposes flatness, separatedness, or nonvanishing on the module.

Dependency declarations read and reused:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`, locally affine locally ringed spaces and
  morphisms of their locally ringed spaces.
- `def-pc-morphism-conventions` is a convention record, with no declaration of
  its own. Its finite-presentation convention is rendered by Mathlib
  `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated`.
- `def-pc-base-change`: `Sheaf.AlgebraicGeometry.BaseChangeConventions` records
  the chosen `Limits.pullback`, its projections, and tensor module pullback.
  Its declaration `Scheme.Modules.moduleBaseChange` is for *iterated* module
  base change between two already base-changed schemes. Here the module starts
  on `Xi` itself, so the underlying recorded `Scheme.Modules.tensorPullback`
  from `Sheaf.AlgebraicGeometry.TensorPullback` is used directly, with no
  duplicate definition or unnecessary identity-base-change comparison.
- `def-weil-pbc-closed-subset-proper-over-base`:
  `Scheme.Modules.HasSupportProperOver` and `Scheme.IsClosedSubsetProperOver`
  in `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`.
- Mathlib `SheafOfModules.IsFinitePresentation`, with its full signature and
  docstring read in `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.

Edge cases checked before writing: an empty index type admits no chosen `i`,
so there is no omitted instance of the node's statement; a singleton system
allows `j = i`. Zero modules and empty schemes are allowed, as are zero rings
at the stages or limit. Proper support includes the empty support. No positivity,
nonemptiness of schemes, characteristic, or independent index universe is imposed.
The index, rings, schemes and module values use the same explicit universe `u`
in accordance with the project's limit-universe convention. All variables and
universes are explicitly bound.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leanfinder`: "Support proper over base descends to a finite
  stage in an inverse limit of affine Noetherian schemes for a finitely presented
  module". Eight hits on affine-transition limits, vanishing sections, and
  Noetherianity; none states proper-support descent.
- `msearch.py ... loogle`: `AlgebraicGeometry.IsProper,
  SheafOfModules.IsFinitePresentation`. Zero hits.
- `msearch.py ... leansearch`: "proper support of a finitely presented sheaf
  descends along an inverse limit of affine schemes". Unavailable: Internal
  Server Error; no mathematical verdict is inferred from service failure.
- `msearch.py ... grep`: `proper.*support|support.*proper|eventually.*proper`
  in `AlgebraicGeometry`. One irrelevant Mathlib morphism-property comment.
- `rg` of both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the
  project's `lean/Sheaf` for proper/support combinations found the existing
  proper-support definition and unrelated cohomology/support statements, but no
  descent theorem. The source search for the node id found no declaration.
- `rg` of `dag/lean_names_upstream.json`, Mathlib, the source and `lean/Sheaf`
  for the proposed theorem name and module name found no collision.
- The existing `EventuallyProper.lean` and `FinitePresentationModuleMapDescent.lean`
  were read for the inverse-system representation and dependency usage.

The repository's Stacks source files are absent on this machine. The source was
read from [Tag 081G](https://stacks.math.columbia.edu/tag/081G) and
[Tag 0CYS](https://stacks.math.columbia.edu/tag/0CYS). The former gives eventual
properness of scheme-theoretic support for finite type quasi-coherent modules;
the latter identifies this with properness of the underlying support. Together
these validate the node's finitely presented specialization. The docstring carries
all four proof steps and their dependency ids. No statement dispute or node fault
was found.

Validation: the server single-file compile passed in 2.4 seconds without errors
or warnings for the initial module. The delivery dry run rechecks the final file
and its metadata; independent second reading is left to the designated reader.

## Second reading by H1

Independent second reader, 2026-10-11. I opened the node copy, the full delivered
module, all four statement-dependency nodes and the declarations they supply.
Verdict: the statement renders the node exactly; no Lean or node repair is needed.
Only this independent review section was added. There are no new definition nodes,
dependency modules, or stage-2 statement corrections in this delivery.

Source check came before the Lean comparison. The local Stacks checkout is absent;
I fetched the upstream `limits.tex` and `coherent.tex` into this item's scratchpad.
I read `situation-descent-property` (Situation 32.8.1),
`lemma-eventually-proper-support` (081G), the surrounding paragraph, and
`lemma-module-support-proper-over-base` (0CYS), together with
`lemma-closed-proper-over-base` (0CYL) and `definition-proper-over-base` (0CYM).
The second source is in `coherent.tex`, despite the item's older source record
naming `cohomology.tex`; that metadata was left untouched. Online cross-checks:
[081G](https://stacks.math.columbia.edu/tag/081G) and
[0CYS](https://stacks.math.columbia.edu/tag/0CYS).
081G assumes affine transitions and qcqs stage schemes, a locally finite type
morphism, and a finite type quasi-coherent module. The node is its stated
Noetherian, finitely presented specialization. In the source situation take
Y_i = S_i and the chosen stage as the initial stage (restrict to its directed
tail). Finite presentation of X_i over affine S_i gives precisely the qcqs
conditions required there. 0CYS identifies proper set-theoretic support with
proper scheme-theoretic support; locally finite type is available by base change.
No separatedness of X_i over S_i or flatness of the module is assumed by the source.

Object/hypothesis/conclusion checklist, extracted from the node before matching:

1. A directed set I: `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]`.
   PASS. A preorder includes all directed partially ordered sets; no linear
   order or countability is imposed. The chosen `i : I` supplies nonemptiness.
2. An inverse system S_k = Spec(R_k), qcqs with affine transitions:
   `(R : I ⥤ CommRingCat.{u})` and `R.op ⋙ Scheme.Spec`.
   PASS. `R.map (homOfLE hij)` runs R_i to R_j; `Spec.map` reverses it
   to S_j to S_i. Every morphism between these affine schemes is affine,
   and every affine scheme is qcqs, so nothing is omitted by their absence
   as separate hypotheses. The functor records identity and composition laws.
3. Each R_k Noetherian: `[∀ k : I, IsNoetherianRing (R.obj k)]`.
   PASS. This is the node's assumption, although the cited generic lemma
   does not itself need it. No condition on the limit ring was introduced.
4. S is their affine inverse limit: `(c : Cone (R.op ⋙ Scheme.Spec))`
   `(hc : IsLimit c) [IsAffine c.pt]`. PASS. `c.pt` is S and the maps are
   `c.π.app (op k)`. `IsAffine` expresses existence of a spectrum presentation;
   it neither chooses a different limit nor imposes a condition beyond
   S = Spec(R) in the node. Any system of affine schemes with given spectrum
   presentations corresponds to such a ring functor through Spec's equivalence.
5. A chosen stage and finitely presented S_i-scheme X_i:
   `(i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))` with
   `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`.
   PASS. I read `def-pc-morphism-conventions`: finite presentation is exactly
   this conjunction, not merely local finite presentation. Its convention
   record requires no new module; the actual Mathlib class signature was read.
6. A finitely presented O_X_i-module F_i:
   `(Fi : Xi.Modules) [Fi.IsFinitePresentation]`. PASS. `Scheme.Modules`
   is `SheafOfModules X.ringCatSheaf`, as read in Mathlib Modules/Sheaf.lean.
   In Quasicoherent.lean:267 the class means locally a cokernel of a map of
   finite free sheaves; the instances at 276 and 281 give quasi-coherence
   and finite type. It is not global finite generation or a vector bundle.
7. X = X_i ×_S_i S and F = pullback of F_i:
   `pullback f (c.π.app (op i))`, with structure map `pullback.snd` and
   `(Scheme.Modules.tensorPullback (pullback.fst ...)).obj Fi`. PASS.
   I read BaseChangeConventions.lean and TensorPullback.lean: the latter is
   O_X tensor over inverse-image O_X_i with inverse-image F_i. The former's
   `moduleBaseChange` is specifically for maps between two base changes,
   so its underlying shared `tensorPullback` is the right declaration here.
   No private pullback definition and no Mathlib `Modules.pullback` is used.
8. Supp(F) proper over S: `hF : Scheme.Modules.HasSupportProperOver ...`.
   PASS. I read ClosedSubsetProperOverBase.lean:49 and its dependency
   `Scheme.IsClosedSubsetProperOver`. The predicate asks for a closed subset
   equal to `{x | ¬ Subsingleton (F.presheaf.stalk x)}` and properness of
   its reduced induced closed subscheme over the given structure morphism.
   It does not require all of X proper or a separately chosen annihilator.
9. Some later stage j ≥ i: `∃ (j : I) (hij : i ≤ j)`. PASS. The quantifiers
   follow the fixed system, cone, stage, scheme, module and support hypothesis;
   the witness may depend on all these objects and `j = i` is allowed.
10. X_j = X_i ×_S_i S_j and its pulled-back F_i has support proper over S_j:
    `pullback f (Spec.map (R.map (homOfLE hij)))`, its `pullback.snd`, and
    `HasSupportProperOver` of `tensorPullback` along its `pullback.fst`.
    PASS. The same Fi and transition map are used throughout; the conclusion
    is precisely proper support at one later stage, with no extra clause.

Edge cases: empty I admits no chosen i, so the theorem has no excluded instance;
a singleton directed system permits its only stage. Zero modules have empty
support and remain permitted. Empty Xi and empty limit schemes, including spectra
of zero rings, are permitted: there is no `Nontrivial` ring or nonempty scheme
hypothesis. Characteristic is unrestricted; n = 0 is inapplicable since no n
occurs. All universes and variables are explicitly bound. The index, rings,
schemes, and module section carriers share `u`, following the project's limit
universe convention; there is no separate small index assumption or test-object
universe making a hypothesis vacuous. Larger presentations can be placed together
in a common larger universe.

Independent searches used different wording from the worker:

- `msearch.py ... leanfinder`: "A coherent sheaf with proper support over a
  limit of spectra of rings has proper support at a sufficiently large index".
  Eight results: limits of sections, vanishing at finite stages, and compact
  closed subsets of limits. None is proper-support descent.
- `msearch.py ... loogle`: `AlgebraicGeometry.IsProper, "limit"`.
  Zero results.
- `msearch.py ... leansearch`: "eventual properness of the support of a
  coherent sheaf under Noetherian approximation". Internal Server Error;
  recorded as unavailable, not evidence of absence.
- Independent `rg` over Mathlib AlgebraicGeometry and sheaves of modules,
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, and repository `lean/Sheaf`
  for `support.{0,60}(descen|eventual|limit)`, the reverse ordering,
  `HasSupportProperOver`, and the proposed declaration name. Only the shared
  proper-support definition and unrelated support/cohomology code appeared;
  no existing theorem matches. This confirms reuse of the definition and
  retention of the delivered new theorem.

H5/H6/H8/H9: the module defines no data and contains exactly one theorem,
whose proof is `by sorry`; no proof was completed. Module and theorem docstrings
name the sources and blueprint id. The proof docstring retains all four node
steps with the corresponding dependencies (scheme-theoretic support and
pullback support; structure independence at the limit; eventual properness;
structure independence at the later stage). Imports serve the definitions and
classes in the signature; namespace, file name and 100-character lines conform.
The node's `lean.statement` is the full verbatim theorem signature before `:=`.
No mismatch in objects, assumptions, quantifiers, or conclusion was found.

Validation: `scompile.py H1 lem-pc-proper-support-descent` on the delivered module
passed with exit code 0, compiled in 2.5 seconds, no errors or warnings.
