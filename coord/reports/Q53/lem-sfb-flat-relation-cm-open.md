## Worker report

The module `Sheaf.AlgebraicGeometry.FlatRelationCMOpen` states
`AlgebraicGeometry.exists_flat_relation_cm_open`, with `sorry` as its only proof.
It formalizes the accepted node without changing its statement, dependency lists,
proof, or split. The inherited unchanged-item failure concerned a stage-1 packet;
the current queue assigns stage 2 and the base node has no Lean record.
The sandbox initially contained only dispatcher brief markers, so there was no
interrupted delivery packet or pushed result to repeat.

Source read: `literature/stacks-project/more-groupoids.tex`,
`lemma-make-CM` (Tag 0460), especially (4) and (5), and
`literature/stacks-project/more-morphisms.tex`, `definition-CM` (Tag 045R).
These assert precisely the open restriction and fibrewise condition used here.

Hypotheses and conclusions, clause by clause:

- The base scheme is `{S : Scheme.{u}}`; the explicit `universe u` implements
  the recorded size convention. The schemes over it are `{V R : Over S}`.
  Thus their structure maps and the fact that the relation maps are over `S`
  are carried by their types, without extra geometric assumptions.
- The two maps of the relation are `(s t : R ⟶ V)`.
  For every test `S`-scheme `T : Over S`, `hinj` asserts injectivity of
  `fun r : T ⟶ R ↦ (r ≫ s, r ≫ t)`. The product of section sets is the
  sections of `V ×[S] V`, so this is the node's sectionwise injectivity.
- `hrel` says `Equivalence` of the relation on `T ⟶ V` whose graph is the
  image of that map: `∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b`.
  It includes reflexivity, symmetry and transitivity for every `T`.
- `[Flat s.left] [Flat t.left]` and
  `[LocallyOfFinitePresentation s.left] [LocallyOfFinitePresentation t.left]`
  are exactly the four stated assumptions on the underlying scheme maps.
- `∃ W : V.left.Opens` chooses an open subscheme; its scheme is
  `W.toScheme` and its canonical open immersion is `W.ι`.
- The first pullback `pullback W.ι t.left` is `W ×[V,t] R`.
  Its map to `V` through `s` is `pullback.snd W.ι t.left ≫ s.left`.
  Pulling this map back along `W.ι` gives exactly
  `pullback (pullback.snd W.ι t.left ≫ s.left) W.ι`, the node's `R_W`.
  No arbitrary model, comparison isomorphism, or extra map is assumed.
- The restricted target projection is
  `pullback.fst (pullback.snd W.ι t.left ≫ s.left) W.ι ≫
  pullback.fst W.ι t.left`. The restricted source projection is
  `pullback.snd (pullback.snd W.ι t.left ≫ s.left) W.ι`.
  The conclusion quantifies over `p` equal to either of these canonical maps.
  This is exactly the conjunction of the same condition for the two maps:
  substituting each map gives its clause, and conversely equality transports
  the respective clause to any `p` satisfying the displayed disjunction.
- For each of these two projections the conclusion gives `Flat p` and
  `LocallyOfFinitePresentation p`. For every `w : W.toScheme` and every
  `x : p.fiber w` it also gives
  `IsNoetherianRing ((p.fiber w).presheaf.stalk x)` and equality between
  `IsLocalRing.depth` of this ring over itself, coerced to `WithBot ℕ∞`, and
  its `ringKrullDim`. These are exactly every local ring of every ordinary
  scheme-theoretic fibre and exactly the node's stated meaning of CM.
  The CM condition is inline; there is no second definition of it.
- The final three conjuncts are `Surjective`, `Flat`, and
  `LocallyOfFinitePresentation` of
  `pullback.snd W.ι t.left ≫ s.left`, namely the specified `h_W`.

Recorded statement dependency declarations used, with their source signatures
and docstrings read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its
  `Scheme.Hom`, the usual locally ringed scheme category.
- `def-weil-size-convention`: the metatheoretic convention has no declaration;
  all schemes, their rings and test schemes use explicit level `u`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd`;
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme pullbacks.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`;
  its recorded stalkwise equivalence `Flat.iff_flat_stalkMap` agrees with
  the node's definition.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber` (the pullback along
  the canonical spectrum of the residue field).
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `WeilConjectures.RingTheory.Depth`: `IsLocalRing.depth`, defined as
  `Ideal.depth` for the maximal ideal, applied to the ring as its own module.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim : WithBot ℕ∞`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Opens.toScheme`, `ι`,
  and the instance that `ι` is an open immersion realize the open subscheme.
- `Mathlib.CategoryTheory.Comma.Over.Basic` supplies the standard category
  of schemes over `S`; `Morphisms.UnderlyingMap` supplies `Surjective`.

The module also imports each recorded, stated proof dependency:
`WeilConjectures.AlgebraicGeometry.RestrictedFibreLocallyNoetherian`,
`WeilConjectures.AlgebraicGeometry.FibreCohenMacaulayLocus`,
`Sheaf.AlgebraicGeometry.CohenMacaulayFieldExtension`,
`Sheaf.TraceFormula.FlatLFPCMLocusFibreDense`, and
`Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties`.
The fibre-base-change match is in the already imported `Fiber`, and the
open-immersion-etale match is imported through `Morphisms.Etale`.
`lem-sfb-relation-open-locus-descent` has no recorded Lean declaration or
Mathlib match, and is used only in the natural-language proof, not the
statement; there is no import to add for it yet. No missing statement
notion or unusable dependency interface was found.

Edge cases checked before writing:

- Empty `V` and `R`: `W = ∅` is permitted, surjectivity onto the empty
  scheme is vacuous, and the fibre-ring conditions have no points to test.
- For nonempty `V`, taking `W = ∅` cannot satisfy the surjectivity conjunct;
  hence the orbit-meeting conclusion is substantive and retained.
- Empty individual fibres have vacuous local-ring conditions; reflexivity
  already forces the original source and target fibres to be nonempty.
- The two restricted maps may coincide: the equality disjunction still
  asserts their common property, with no distinctness assumption.
- Non-Noetherian, non-quasi-compact and nonseparated bases remain allowed.
  No characteristic, separability, dimension, reducedness or field
  hypothesis has been introduced. No independent smaller test universe
  makes the relation assumption vacuous.
- Depth is compared in `WithBot ℕ∞` by the standard coercion; dimension zero
  and unbounded dimensions are not removed. A local ring at an actual
  scheme point is nonzero, consistent with the dimension convention.

Searches for an existing statement (all run for this item with `msearch.py`):

- `leanfinder`: "A flat locally finitely presented scheme equivalence relation
  has a Cohen Macaulay open restriction meeting every orbit". Eight hits,
  headed by `UniversallyOpen.of_flat`, `IsOpenImmersion.of_flat_of_mono`,
  `Flat`, and smooth-locus lemmas; none gives the asserted relation theorem.
- `loogle`: `"AlgebraicGeometry.Flat", "CohenMacaulay"`. No hits.
- `grep`: `[Cc]ohen.?[Mm]acaulay|[Ee]quivalence[Rr]elation.*[Ff]lat`.
  No Mathlib hits.
- `leansearch`: "A flat locally finitely presented equivalence relation on
  schemes has an open restriction with Cohen Macaulay projections and
  surjective saturation". Eight hits concerning flat open restrictions,
  universal openness and affine flatness; none states the relation theorem.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for CohenMacaulay,
  cohenMacaulay, schemeRelationRestriction, and sectionwise-equivalence
  patterns found the existing depth-equals-dimension results and the
  sectionwise-relation conventions in `EtaleRelationKernelPair` and
  `EtaleRelationFindingOpens`, but no CM open-restriction theorem.
  Searching the item id in `lean/WeilConjectures` found no declaration.
- Mathlib source `rg` for CM and relation/CM combinations likewise found
  no existing CM theorem; the existing depth, dimension and fibre APIs
  are reused instead of introducing new notions.

Validation: `scompile.py Q53 lem-sfb-flat-relation-cm-open` compiled the
single delivered module in both sandbox and library context, with no errors
or warnings (9.3 s and 8.7 s). The module has only the named theorem above,
with an explicit six-step proof docstring reproducing the node's proof plan.
There is no statement dispute, correction, new node, or dependency repair.

## Second reading by Q53

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
