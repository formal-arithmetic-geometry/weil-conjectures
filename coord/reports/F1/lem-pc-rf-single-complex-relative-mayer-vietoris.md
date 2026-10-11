## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeMayerVietoris` states the relative
Mayer--Vietoris induction step from Stacks Tag 0DJ9. It binds a cartesian square
through `IsPullback g' f' f g`, affine bases, quasi-compact and quasi-separated
`f`, four derived-category instances, a derived object `K`, a target object
`K'`, and a morphism `φ : L(g')^*K ⟶ K'`. It uses opens `U,V : X.Opens`,
quasi-compact open immersions, the cover equation `U ⊔ V = ⊤`, and the
three local comparison isomorphism hypotheses (each followed by the local
map induced by `φU`, `φV`, or `φUV`). The conclusion is that the global
canonical comparison followed by the map induced by `φ` is an isomorphism.
All proofs are `sorry`.

The dependency module `Sheaf.AlgebraicGeometry.DerivedBaseChangeMap` supplies
`AlgebraicGeometry.derivedBaseChangeMap`, the adjoint mate of the unit for `g'`
followed by the canonical direct-image composition comparisons, and
`derivedBaseChangeMapOnOpen` for an open `W` and its inverse image. It imports
`DerivedAdjoint` and `DerivedDirectImageCompositionUnbounded`, using
`nonempty_derivedPullbackAdjunction` and `derivedDirectImageComposition`.

The direct-image dependency is available through the landed
`Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage` declaration; no private
replacement was made. The item additionally cites
`def-pc-derived-base-change-map`, whose previous node had no Lean declaration;
the dependency module is included because its notion is needed to type every
comparison map.

Edge cases checked: `U`, `V`, and `U ⊓ V` may be empty; `K` and `K'` may be
zero objects; no nonemptiness or separatedness beyond the stated hypotheses is
introduced; the universe is shared by schemes and open subschemes. The affine
assumptions are exactly those in Tag 0DJ9's induction reduction.

Searches made: `msearch.py leanfinder` for “derived base change map schemes”
returned only generic pullback-property declarations; `msearch.py loogle`
for `Adjunction.homEquiv, Functor.isoWhiskerLeft` returned no hit;
`msearch.py grep` for `MayerVietoris|derivedBaseChange` in Mathlib AlgebraicGeometry
returned no matching derived O-module statement; `rg` over WeilConjectures and
`lean/Sheaf` found only etale/pro-étale base-change maps and no declaration of
this node. The Stacks pages for Tags 0DJ9, 08HY, and 02N7 were read directly.
No STATEMENT-DISPUTED issue was found.

## Earlier second reading (a previous round; superseded)

The second reading is reserved for the independent reader. The worker checked that
all binders are explicit, all three local comparison hypotheses and the global
composite are present, and the module compiles cleanly with no warnings.

## Dependency modules

`def-pc-derived-base-change-map` had no recorded Lean declaration. The module
now defines the canonical adjoint base-change map and the restriction map for an
open and inverse image, using the recorded derived adjunction and direct-image
composition declarations. Its `lean.note` records this reason.

## Statement corrected

The original node did not explicitly introduce `K'` before using it in the map
`L(g')^*K → K'`, and it did not make explicit that the three local maps are
restrictions of this same map. Following Tag 0DJ9, the corrected statement
introduces `K' ∈ D_QCoh(O_X')` and specifies restriction through the canonical
pullback composition isomorphisms. The citer
`lem-pc-rf-single-complex-qcqs-induction` still holds: it supplies exactly such a
map and uses the global conclusion.

The related node `lem-pc-rf-mv-triangle-naturality` is also compatible: it already
introduces both quasi-coherent complexes and the canonical restrictions of the
same morphism. Its broader reference to this gluing node is unaffected.

## Second reading by F1

I read the corrected statement first against perfect.tex,
`lemma-single-complex-base-change` (Tag 0DJ9), especially its affine reduction
and induction step. The source introduces K' implicitly as the target of a
map in D_QCoh; explicitly binding it and transporting restrictions of that
same map makes the node self-contained without changing its meaning. I opened
the citer and a second related node: `lem-pc-rf-single-complex-qcqs-induction`, proof step 4, supplies
the three local isomorphisms after restricting to U union V; and
`lem-pc-rf-mv-triangle-naturality` already states the same objects and canonical
restriction maps. The citer holds verdict is true; the related node is compatible too.
The dry-run validator confirmed that only the induction node cites this item
in stmt_deps or proof_deps on the current base. The naturality node mentions
it elsewhere, so it is not included in statement_change.citers.

Clause-by-clause reading (objects and hypotheses precede the conclusion):

- Four schemes and four morphisms: `{X S X' S' : Scheme.{um}}` and
  `f,f',g,g'`. PASS: these are Mathlib schemes, not varieties over a field.
- Commutative cartesian square: `h : g' ≫ f = f' ≫ g` and
  `hpull : IsPullback g' f' f g`. PASS: arbitrary pullback presentation,
  not an equality with a chosen fibre product.
- Affine bases: `[IsAffine S] [IsAffine S']`. PASS: the source's affine
  reduction preceding the induction step, no affine assumption on X or X'.
- Quasi-compact and quasi-separated f: `[QuasiCompact f] [QuasiSeparated f]`.
  PASS: no Noetherian, properness, separatedness or flatness assumption.
- K and K' in D_QCoh: `K`, `hK : schemeDerivedQCohProperty X K`,
  `K'`, `hK' : schemeDerivedQCohProperty X' K'`. PASS: DerivedCategory.lean
  defines the property by quasi-coherence of every integer cohomology sheaf.
  Using ambient objects plus their property is the full-subcategory encoding.
- One input map: `φ : (derivedPullback g').obj K ⟶ K'`. PASS: the recorded
  tensor-derived pullback, not Mathlib's underived right-adjoint pullback.
- Two opens and three quasi-compactness hypotheses: `U V : X.Opens`,
  `hUqc`, `hVqc`, `hUVqc` are IsCompact of U,V,U meet V. PASS: quasi-compact
  in the topological sense, with no Hausdorff condition.
- Cover: `hcover : U ⊔ V = ⊤`. PASS: exactly X=U union V.
- W'=X' times_X W: `pullback g' W.ι`, with `pullback.fst` to X' and
  `pullback.snd` to W. PASS: checked the projection orientation; composition
  with f' gives f' restricted to W'. The inverse-image-open version in
  `derivedBaseChangeMapOnOpen` is the isomorphic open presentation.
- Each local comparison: `hU`, `hV`, `hUV` apply `derivedBaseChangeMap` to
  the restricted square, followed by derived direct image of
  `derivedBaseChangeRestriction g' W φ`. PASS: all three hypotheses use the
  same φ, transported by the recorded pullback composition comparisons.
- Global conclusion: `IsIso (derivedBaseChangeMap f f' g g' h K ≫
  (schemeDerivedDirectImage f').map φ)`. PASS: precisely the claimed
  canonical composite, with no extra conclusion.
- Localization choices: the family of `HasDerivedCategory.{wm}` instances
  is the same infrastructure required by DerivedPullbackComposition.lean.
  It chooses localizations, not geometric hypotheses; the standard
  HasDerivedCategory construction supplies the family in a large enough
  universe. All scheme universes and both named universe variables are bound.

Dependency reading: I opened the statements and modules for scheme,
base change, derived category, derived pullback, scheme derived direct image,
derived adjunction and derived pullback composition, and the direct-image
composition theorem. SchemeDerivedDirectImage.lean uses the recorded
ringed-space unbounded construction, not bounded-below cohomology.
There are no new definition nodes. The one delivered dependency is
`def-pc-derived-base-change-map`; I read its unit/composition formula against
cohomology.tex `remark-base-change` (08HY) and sites-cohomology.tex
`remark-base-change` (07A7), together with the adjunction construction in
0736. The source admits all commutative squares and unbounded objects, so the
definition's general domain extends its cartesian QCoh use without changing
that use. 02N7 alone would assume flatness and boundedness; I replaced that
module-level citation by 0D5T and retained the node's 07A7/0736 citations.

Mismatch repaired: `derivedDirectImageComposition` only gives Nonempty Iso;
choosing that existential does not constrain the comparison to the canonical
one. The dependency now constructs both direct-image comparisons with
`conjugateIsoEquiv`, using the same chosen derived adjunctions and the canonical
comparison from `exists_derivedPullbackComposition`. The unit mate formula is
otherwise unchanged. This also aligns the compositions with those used to
restrict φ. The dependency uses the shared localization family required by
that recorded composition theorem; redundant per-open instance binders and
the now-unused import were removed. The dependency's lean.statement was
regenerated verbatim from its declaration. The main theorem was left intact.

Edge cases: empty U,V and empty overlap are allowed, including X empty and
an empty base; zero K or K' and the zero map are allowed. The three isomorphism
hypotheses are still required in those cases. No nonempty index type is used.
There is no natural-number degree, rank or characteristic restriction;
unbounded complexes include all integer degrees. Schemes may be lifted to a
common arbitrary universe; wm remains independent of um. No hollow data,
private notions, file-local notation or proved auxiliary theorem was added.
The only theorem proof in the delivery is the required sorry. Its docstring
contains all four proof steps with the named DAG dependencies.

Independent searches: LeanFinder “derived direct image open cover gluing
isomorphism” returned gluing of presheafed spaces and opens, not this result.
Loogle “IsIso, IsPullback” could not resolve the unqualified identifier; this
is not evidence of absence. LeanSearch “unbounded derived base change sheaves
modules schemes” was unavailable (Internal Server Error). Mathlib grep
“baseChange|MayerVietoris” in AlgebraicGeometry found geometric stability
results, not derived O-module comparisons. I also used rg for
“derivedBaseChange”, “relativeMayer”, “base.change.*(adjoint|unit)” and
“MayerVietoris” in WeilConjectures, Mathlib AlgebraicGeometry and lean/Sheaf.
The derived base-change hits concern etale/pro-etale coefficient sheaves;
the landed DerivedDirectImageComposition.lean is bounded-below etale, not
unbounded O-module direct image. DerivedMayerVietorisTriangle.lean states
the input triangles, not the single-complex gluing comparison. None is an
existing realization of this node or the supplied dependency.

Validation: both delivered modules compiled together in dependency order
with scompile.py, exit 0, 17.9 seconds, no warnings. Signatures were checked
for bound variables and line lengths at most 100 characters.
