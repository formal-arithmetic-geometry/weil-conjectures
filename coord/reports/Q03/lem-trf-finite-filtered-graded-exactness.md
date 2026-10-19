## Worker report

The module `Sheaf.Paper.FiniteFilteredGradedExactness` records the canonical
filtration-step, graded-piece, and quotient maps for `PBCFilteredObject`, and
states `CategoryTheory.PBCFilteredObject.finite_filtered_graded_exactness` with
one postponed proof. The source is Stacks Project, Homology, Tag 05QH,
`lemma-filtered-acyclic`, parts (1)--(5), with the finite filtration notion from
Tag 0121. No existing declaration states this theorem.

The node's ambient abelian category is rendered by the explicit module
variables `{C : Type u} [Category.{v} C] [Abelian C]`; the universes are bound.
The recorded dependency `def-sp-filtration` is used through its upstream
`CategoryTheory.PBCFilteredObject` and `CategoryTheory.PBCDecreasingFiltration`
and the existing restriction/graded-map declarations in
`WeilConjectures.CategoryTheory.PBCFiniteFiltrationInduction`. The Mathlib leaf
`def-sp-abelian` is `CategoryTheory.Abelian` from
`Mathlib.CategoryTheory.Abelian.Basic`, supplied by that import.

Hypothesis and conclusion correspondence:

- `X`, `Y`, and `Z` are exactly `PBCFilteredObject C`, so their objects and
  decreasing filtrations are the recorded filtered objects. `u : X ⟶ Y` and
  `v : Y ⟶ Z` are exactly filtration-preserving morphisms in the recorded
  category. `hvu : u.hom ≫ v.hom = 0` is the node's `vu=0` condition.
- `hX`, `hY`, and `hZ` state
  `PBCDecreasingFiltration.IsFinite X.filtration`, and similarly for `Y` and
  `Z`; this is the recorded finite (two endpoint bounds) condition.
- The existing `restriction f p` is the induced map
  `F^p A -> F^p B`, obtained from the actual witness in `f.preserves p`.
  The upstream declaration records its factorization through the target
  subobject. Its `Classical.choose` is on the data field of the filtered
  morphism; the factor is uniquely determined because the target filtration
  arrow is mono.
- `PBCDecreasingFiltration.gradedPiece` is exactly `F^p/F^(p+1)`. The
  definition `gradedMap` is the induced cokernel map, with its required
  well-definedness recorded as the named theorem `gradedMap_condition`.
  Thus `hgr` says that for every integer `p`, the canonical sequence
  `gradedMap u p`, `gradedMap v p` is `ShortComplex.Exact`.
- `PBCFilteredObject.IsStrict f` says for every `p` that the image of the
  restriction map, represented as
  `imageSubobject (stepMap f p ≫ (B.filtration.step p).arrow)`, equals
  `imageSubobject f.hom ⊓ B.filtration.step p`, i.e. exactly
  `f(F^pM)=im(f)∩F^pN`.
- `quotientObject A p` is the cokernel of the filtration subobject arrow,
  hence `A/F^pA`. `quotientMap f p` is the induced map on these quotients;
  `quotientMap_condition` records that the map factors through the target
  cokernel.
- The conclusion's first two conjuncts are strictness of `u` and `v`.
  The third is exactness of the underlying sequence, represented by
  `ShortComplex.mk u.hom v.hom hvu`.
- The final `∀ p` gives both requested exact sequences. The first uses
  `restriction u p` and `restriction v p`, and the second uses `quotientMap u p` and
  `quotientMap v p`. The named compatibility theorems
  `restriction_comp` and `quotientMap_comp` supply their square-zero proofs.
  The local `gradedMap_comp` supplies the square-zero proof used in `hgr`.

The helper definitions have genuine data: the recorded upstream `restriction`
and `gradedMap` choose factors supplied by a filtered morphism and its cokernel
universal property; local `quotientObject` is a cokernel and `quotientMap` uses
the cokernel universal map. The named compatibility and well-definedness
results are the only postponed helper theorems; no `sorry` appears as
definition data. The main theorem proof is `by sorry`, as required
for stage 2. Every declaration has the source and blueprint id in its
docstring.

Dependencies read:

- `WeilConjectures.CategoryTheory.PBCFiltration`, declarations
  `CategoryTheory.PBCFilteredObject` and `CategoryTheory.PBCDecreasingFiltration`,
  including `Hom`, `preserves`, `step`, `antitone_step`, and `gradedPiece`; and
  `WeilConjectures.CategoryTheory.PBCFiniteFiltrationInduction`, declarations
  `CategoryTheory.PBCFilteredObject.restriction`, `gradedMap`, and
  `exists_gradedMap`. These are the recorded `def-sp-filtration` interfaces.
- `Mathlib.CategoryTheory.Abelian.Basic`, declaration
  `CategoryTheory.Abelian`, the recorded `def-sp-abelian` match.
- The proof dependency `lem-weil-pbc-complex-ses-homology-long-exact` is a
  Mathlib leaf whose recorded match is
  `CategoryTheory.ShortComplex.ShortExact.homology_exact₂`; it is used by the
  proof plan and therefore is not restated in this module.
- Mathlib `CategoryTheory.ShortComplex`, `ShortComplex.mk`, `ShortComplex.Exact`,
  subobject images/intersections, and cokernel maps are used directly.

Edge cases checked before writing: the zero category and all-zero objects make
all endpoint and exactness clauses vacuous in the expected way; a filtration
with one nonzero graded piece is covered by the arbitrary integer `p` binder;
`u=0` and `v=0` retain the stated strictness and exactness requirements; a
filtration step outside the common finite bounds is represented by the existing
filtration and its zero/top endpoint clauses; `p=0` is not singled out or
excluded; and no characteristic, nonemptiness, or extra universe restriction is
introduced. The finite bounds are independently supplied for `X`, `Y`, and `Z`,
so the proof may choose common bounds as in the source.

Searches made on 2026-10-17:

- `msearch.py ... leanfinder` query “finite filtered abelian category graded exact strict maps
  filtration steps quotient exact”: eight hits, including ordinary `ShortComplex` exactness and
  unrelated finite exactness; no finite-filtered graded theorem.
- `msearch.py ... loogle` query “CategoryTheory.ShortComplex.Exact,
  CategoryTheory.PBCFilteredObject, gradedPiece”: zero hits (the project declaration is not
  Mathlib).
- `msearch.py ... grep` query “finite.*filtered|graded.*exact|strict.*filtration” in
  `Mathlib/CategoryTheory`: zero hits.
- `rg` over the upstream `WeilConjectures` source and project `lean/Sheaf` for
  `finite_filtered_graded_exactness`, `gradedMap`, `quotientMap`, and
  `IsStrict`: no declaration of this statement; hits for `IsStrict` were
  unrelated homological-complex bounds.
- Literal node-id search in the upstream/project source found no declaration;
  DAG search found only this node and its two downstream citers.

The existing searches recorded in the node (LeanFinder, LeanSearch, Loogle, and
Mathlib grep) likewise found only ordinary exactness or unrelated filtrations.
No `STATEMENT-DISPUTED` flag, dependency repair, new node, or statement
correction is needed.

## Earlier second reading (a previous round; superseded)

I reread the complete node and module after compilation. `hvu` has the same
orientation as the node's `vu=0`; all three finite hypotheses are present; and
`hgr` quantifies over every integer and uses the canonical cokernel graded maps.
The conclusion has both strictness clauses, underlying exactness, and both the
filtration-step and quotient exactness clauses for every integer. The strictness
equality is rendered as image of the restricted map equal to image intersected
with the target filtration step. The quotient is the cokernel of the actual
subobject arrow, not an arbitrary quotient object. The induced maps use the
recorded filtered-morphism preservation data, and their compatibility proofs
are named postponed theorems rather than hidden proof terms in definitions. No
hypothesis or edge case from the node was added or omitted, and the theorem
compiled cleanly through `scompile.py`.

## Second reading by Q03

I read the node JSON, Stacks `homology.tex` at Tag 05QH (`lemma-filtered-acyclic`),
the filtration definition at Tag 0121, the recorded declarations for
`def-sp-abelian` and `def-sp-filtration`, and the complete Lean module.

The node statement parses as follows, with the corresponding Lean rendering and verdict:

- The ambient object is an abelian category `A`. Lean binds `{C : Type u}` with
  `[Category.{v} C] [Abelian C]`; both universes are explicit and no extra structure is
  assumed. This is the recorded `CategoryTheory.Abelian` notion.
- The objects are filtered objects `X`, `Y`, `Z`, and the maps are filtration-preserving
  `u : X ⟶ Y`, `v : Y ⟶ Z`. Lean uses `PBCFilteredObject C` and its recorded category,
  so the underlying objects, decreasing integer-indexed filtrations, and preservation
  witnesses are the dependency declarations themselves.
- The complex condition `vu = 0` is exactly
  `hvu : u.hom ≫ v.hom = 0`, with the same order of composition.
- Finite decreasing filtrations on all three objects are exactly the separate hypotheses
  `PBCDecreasingFiltration.IsFinite X.filtration`, and likewise for `Y` and `Z`.
- “Strict” is rendered by the module's inline `PBCFilteredObject.IsStrict`: for every
  `p : ℤ`, the image of the canonical restriction followed by the target step inclusion
  equals `imageSubobject f.hom ⊓ B.filtration.step p`. This is the subobject equation
  `f(F^pM) = im(f) ∩ F^pN` from the node, using the canonical `restriction` factor.
- The graded hypothesis is `hgr : ∀ p : ℤ, ...Exact`, where the two maps are the
  dependency's canonical cokernel maps `gradedMap u p` and `gradedMap v p`; the named
  `gradedMap_comp` supplies exactly the required zero composite. Thus every integer p is
  quantified, including p = 0 and all endpoint or zero graded pieces.
- The first conclusion conjuncts `IsStrict u` and `IsStrict v`, exactly the two strictness
  clauses of Tag 05QH(4).
- The third conjunct is
  `(ShortComplex.mk u.hom v.hom hvu).Exact`, which is exactness of the underlying
  sequence `X → Y → Z` in the ambient abelian category (Tag 05QH(5)).
- For every `p`, the final conjunct contains exactness of the canonical step maps
  `restriction u p`, `restriction v p`, and exactness of the canonical quotient maps
  `quotientMap u p`, `quotientMap v p`. `quotientObject A p` is the cokernel of the
  actual filtration-step subobject arrow, so it denotes `A/F^pA`; the induced maps and
  their square-zero equation are named declarations in this module. This is precisely
  Tag 05QH(2) and (3), with no missing clause or changed quantifier order.

The edge cases remain covered: the zero category and zero filtered objects satisfy the
same typed clauses; a one-step filtration and a step outside the finite bounds are
included by the unrestricted integer quantifier; `u = 0` or `v = 0` is not excluded; and
no characteristic, nonemptiness, or universe equality is imposed. `IsFinite` is exactly
the source's existential whole-object and zero-step condition, with independent bounds
for X, Y, and Z.

I searched Mathlib and the upstream/project Lean sources with LeanSearch, LeanFinder,
Loogle, `rg`, and the recorded `msearch.py` queries for finite filtered graded
exactness, strict filtered maps, `PBCFilteredObject`, `gradedMap`, and the node id.
Only ordinary exactness or unrelated filtration declarations were found; there is no
existing statement or matching definition. The dependency declarations are used directly,
and no new node, dependency repair, statement correction, or `STATEMENT-DISPUTED` flag is
needed. The only postponed proofs are the named compatibility/well-definedness theorems
and the main theorem, while all definition data is canonical (restriction factors,
cokernels, and cokernel-desc induced maps). `scompile.py` compiled the module with no
errors or warnings.

## Maintainer review fix (2026-10-17)

The mathematics of the delivered statement was correct and is kept clause by clause. The
module was restated on the recorded `def-sp-filtration` interface (H4). At the base of this
delivery that record is upstream `CategoryTheory.DecreasingFiltration` (Q01, 2026-10-17),
with filtered objects `CategoryTheory.FilteredObject` and the category of
`FilteredObject.HomPreservingSteps` in `Sheaf.CategoryTheory.Filtration`. The canonical
step and graded maps are `FilteredObject.restrictionSteps` and `FilteredObject.gradedMapSteps`
in `Sheaf.CategoryTheory.FiniteFiltrationInduction`. The delivery had used the superseded
parallel copy `PBCFilteredObject`/`PBCDecreasingFiltration`. The landed citer
`lem-trf-filtered-localization-injective-model` (`FiniteFilteredObjects` over
`FilteredObject`) could not apply a lemma stated on that copy.

Changes: `PBCFilteredObject` → `FilteredObject`, `PBCDecreasingFiltration.IsFinite` →
`DecreasingFiltration.IsFinite`, `restriction`/`gradedMap` → `restrictionSteps`/`gradedMapSteps`,
and helper names `restrictionSteps_comp`/`gradedMapSteps_comp`; the namespace is
`CategoryTheory.FilteredObject`. The file is now a `module` file with `public import` and
`@[expose] public section`, like every landed `Sheaf` module (a non-module file cannot be
imported by module files). The proof plan of the node is written out step by step in the main
docstring, and each helper theorem has a proof sketch. The module path is unchanged.
