## Worker report

The module `Sheaf.CategoryTheory.PosetFilteredCofibrantResolution` defines the
full lower simplicial subcategory, its inclusion, its restriction map, the
objectwise morphism property, and the lower-subcategory diagram.  It states
`CategoryTheory.CoherentNerve.poset_filtered_cofibrant_resolution` with the
required `sorry` proof.  The natural-language node and all of its fields are
unchanged.  No new definition node or dependency repair is needed.

The source is Lurie, *Higher Topos Theory*, Definition A.3.5.7 and Lemma
A.3.5.9, printed pp. 894--895 (PDF pp. 911--912), as recorded in the node.
The module header and every declaration docstring cite that source and the
blueprint item.

Hypothesis and conclusion correspondence:

- The small poset is `(A : Type u) [PartialOrder A]`; the simplicial category is
  `(C : SCat.{u})`; and its grade is `(d : C → A)`.  The common universe is
  explicit, and no directedness, well-foundedness, nonemptiness, or top element
  is added.
- The forbidden-grade hypothesis is exactly
  `hd : ∀ x y : C, ¬ d x ≤ d y → ∀ n : SimplexCategoryᵒᵖ,
  IsEmpty ((hom C x y).obj n)`.  Thus every simplicial degree of a forbidden
  mapping set is empty, including degree zero.
- `B : CategoryTheory.BergnerModelData.{u}` supplies the specified Bergner
  fibrations.  `M : ModelCategory (A ⥤ SCat.{u})` is the projective model
  structure witness.  `hW` identifies its weak equivalences with
  `posetFilteredObjectwise SSet.Bergner.dwyerKanEquivalences`, and `hF`
  identifies its fibrations with the objectwise `B` fibrations.  These are the
  explicit Lean witnesses for the node's assumption that the projective model
  structure has the stated objectwise classes.
- The conclusion chooses `C' : SCat.{u}` and `f : C' ⟶ C`; the first conjunct,
  `Function.Bijective f.obj`, is bijectivity on objects.
- The second conjunct says, for every `x y : C'`,
  `SSet.modelCategoryQuillen.I.rlp (f.map x y)`, exactly the generating-
  cofibration lifting characterization of a trivial Kan fibration.
- The third conjunct repeats the grade condition for the resolved mapping
  sets: if `¬ d (f.obj x) ≤ d (f.obj y)`, every degree of
  `(hom C' x y)` is `IsEmpty`.
- The fourth conjunct is the projective cofibrancy lifting property.  For every
  diagram map `p : X ⟶ Y`, objectwise fibrations and Dwyer--Kan equivalences
  `(∀ a, B.model.categoryWithFibrations.fibrations (p.app a) ∧
  SSet.Bergner.dwyerKanEquivalences (p.app a))` imply that every natural map
  `g` from the lower diagram has a lift `l` with `l ≫ p = g`.
- The fifth conjunct is the Dwyer--Kan equivalence of `f`.
- The final universal conjunct is the Dwyer--Kan equivalence of every lower
  restriction, using the actual full-subcategory map
  `posetFilteredFullSubcategoryMap f` with the displayed predicates and proof
  that an object below `a` remains below `a`.

The helper definitions render the node's constructions without private copies:
`posetFilteredFullSubcategory` uses the original mapping simplicial sets and
restricted objects; `posetFilteredFullSubcategoryInclusion` is the canonical
identity-on-mapping inclusion; `posetFilteredFullSubcategoryMap` restricts an
enriched functor; `posetFilteredObjectwise` is the pointwise morphism property;
and `posetFilteredLowerDiagram` uses the identity functor on `C` and the order
map `leOfHom` for its transition maps.  Empty predicates and equal grades are
therefore represented literally.

Dependency declarations used:

- `Sheaf.CategoryTheory.SimplicialInversionUniversalProperty`, declaration
  `CategoryTheory.SimplicialInversion.simplicial_inversion_universal_property`
  (the recorded statement dependency and the source of the Bergner model
  data and Dwyer--Kan convention).
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`, declaration
  `SSet.KanQuillen.right_proper_kan_quillen` (the recorded statement dependency,
  including `SSet.modelCategoryQuillen.I.rlp` and Kan trivial fibrations).
- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`, declaration
  `SSet.Bergner.simplicial_interval_lifting` (proof dependency; fixed-object
  model structure, generators, and small-object infrastructure).
- `Sheaf.CategoryTheory.ArrowCellWordFiltration`, declaration
  `CategoryTheory.CoherentNerve.arrow_cell_word_filtration` (proof dependency;
  the word presentation used to preserve grades under arrow attachments).
- Mathlib `Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument`
  (the mathlib match for `lem-coef-small-object-cell-factorization`; it supplies
  the small-object cardinality interfaces used in the proof docstring).
- The proof docstring also cites `lem-coef-fixed-object-free-arrow-adjunction`
  and `lem-coef-scat-fixed-object-pushout-comparison`, whose nodes are already
  recorded but have no landed Lean declaration; consequently they are cited in
  the proof plan but not imported as nonexistent modules.  No dependency
  statement is restated or altered.

Edge cases checked before writing and while checking the signature: `A` may be
empty; `C` may have no objects; lower predicates may be empty; `a` need not be a
least or greatest grade; equal grades and loops are allowed; forbidden mapping
sets are empty in every simplicial degree; degree `n = 0` is included; and the
object bijection permits an empty object set.  No hypothesis silently excludes
these cases.  The transition maps of the lower diagram are identity on the
underlying simplicial category and use only transitivity of `≤`.

Searches for an existing declaration were made with the prescribed tools:

- `msearch.py NH ... leanfinder` for “A simplicial category graded by a poset
  admits a same-object resolution with trivial Kan fibrations on mapping sets
  and projectively cofibrant lower subcategories”: eight generic hits
  (`CategoryTheory.SimplicialCategory`, Bergner model-category declarations,
  and generic cofibrant resolutions), with no exact theorem.
- `msearch.py NH ... loogle HomotopicalAlgebra.IsCofibrant`: twelve generic
  cofibrancy hits and no fixed-object poset-filtered resolution.
- `msearch.py NH ... grep projective.*cofibrant|cofibrant.*filtrat|Bergner`
  in `AlgebraicTopology`: zero hits.
- Direct `rg` searches in the upstream `WeilConjectures` source and shared
  `lean/Sheaf` for the item id, `posetFiltered`, and the theorem name found no
  existing declaration.  The only matching source is this sandbox module.
  The node's recorded mathlib searches likewise found no exact definition or
  theorem; their complete tool records are retained in `searches.jsonl`.

Validation: `scompile.py NH lem-coef-poset-filtered-cofibrant-resolution`
compiled the module and its library copy cleanly with no errors or warnings.
The theorem has exactly the expected postponed proof (`sorry`); all helper
definitions have real data.  No `STATEMENT-DISPUTED` flag or node fault was
found.

## Second reading by NH

I independently re-read the node statement, the module signature, the helper
definitions, and both recorded statement dependencies.  The binders and
universes match the node; `hd`, `hW`, and `hF` are rendered clause-for-clause;
the four resolution properties, the projective lifting clause, the global
Dwyer--Kan equivalence, and every lower restriction are all present.  The
identity and composition proofs of the lower diagram compile definitionally.
I found and repaired the only elaboration issue in the interrupted draft:
those proofs now use `rfl` and unused binders are named `_a`, `_f`, and `_g`,
so the clean compile has no warnings.  No mathematical mismatch remains.

## Maintainer review correction (stage-2 reviewer, 2026-10-17)

One definition per notion (H4): the delivered helper `posetFilteredObjectwise`
was a private copy of Mathlib's `CategoryTheory.MorphismProperty.functorCategory`
(`fun _ _ f ↦ ∀ j, W (f.app j)`), which the project already uses for objectwise
classes of diagram model structures (e.g. `SimplicialPresheafProjectiveModel`,
`BrownReedyDiagrams`).  The helper is removed and `hW`, `hF` now read
`SSet.Bergner.dwyerKanEquivalences.functorCategory A` and
`B.model.categoryWithFibrations.fibrations.functorCategory A`.  The two
properties agree definitionally (`Iff.rfl` checked), so the statement is
unchanged in content; the mentions of `posetFilteredObjectwise` above refer to
the delivered version.  The corrected module compiles cleanly with
`tools/nt_compile.py` (no error, no warning).
