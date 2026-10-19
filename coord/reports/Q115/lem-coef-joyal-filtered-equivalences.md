## Worker report

The module `lean/Sheaf/AlgebraicTopology/JoyalFilteredEquivalences.lean` states
`SSet.categorical_equivalences_colimMap_of_isFiltered`. It uses the model structure
`M : HomotopicalAlgebra.ModelCategory SSet.{u}` and its Joyal characterization
`hJoyal`, supplied by `SSet.exists_joyal_model_structure` from
`Sheaf.AlgebraicTopology.JoyalModelStructure`. For a small filtered category `J`,
two diagrams `X Y : J ⥤ SSet.{u}`, and a natural transformation `a : X ⟶ Y`,
the hypothesis `ha` says that every component `a.app j` is a Joyal weak
(categorical) equivalence, expressed as membership in
`M.categoryWithWeakEquivalences.weakEquivalences`; the conclusion says the canonical
Mathlib map `colimMap a` has the same property. The theorem is universe-polymorphic
in `u` (with the independent testing universe `v` in `hJoyal`), which gives the
asserted enlargement-of-universe clause by re-instantiation. A filtered union of
simplicial subsets is the special case where the transition maps are degreewise
injective; the colimit map remains exactly `colimMap a`.

The Lean rendering of each part is:

* “Joyal model structure and categorical equivalences” is `M` together with
  `hJoyal`, whose right side is the `hoFunctor` equivalence test against every
  `C : SSet.{max u v}` with `C.Quasicategory`.
* “small filtered ordinary category” is `(J : Type u) [SmallCategory J]
  [IsFiltered J]`; `SmallCategory` supplies the ordinary small category and
  `IsFiltered` supplies nonemptiness, common cocones for pairs of objects, and
  eventual equalization of parallel arrows.
* “diagrams” and “natural transformation” are `(X Y : J ⥤ SSet.{u})` and
  `(a : X ⟶ Y)`.
* “every component is a categorical equivalence” is
  `ha : ∀ j : J, M.categoryWithWeakEquivalences.weakEquivalences (a.app j)`.
* “induced degreewise colimit map” is Mathlib’s canonical `colimMap a`, with
  colimits in `SSet` computed degreewise.
* “the induced map is a categorical equivalence” is
  `M.categoryWithWeakEquivalences.weakEquivalences (colimMap a)`.
* The statement is uniform in `u`; this is the Lean form of the final universe
  enlargement clause. The filtered-union sentence is recorded in the module
  documentation as the monomorphism-transition special case of the same theorem.

Dependency declaration used: `Sheaf.AlgebraicTopology.JoyalModelStructure`,
`SSet.exists_joyal_model_structure`. Mathlib declarations used are
`CategoryTheory.Limits.colimMap`, `CategoryTheory.SmallCategory`, and
`CategoryTheory.IsFiltered` from `Mathlib.CategoryTheory.Filtered.Basic` and
`Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`.

Edge cases checked: `IsFiltered` includes nonemptiness; parallel arrows need only
become equal after postcomposition; transition maps need not be injective, so the
statement includes arbitrary filtered diagrams and hence also filtered unions. Empty
simplicial sets and degree-zero simplices are allowed by `SSet` and by the unrestricted
`colimMap`; no quasicategory or fibrancy assumption is imposed on `X` or `Y`. The
universe parameter is not fixed, so the same declaration can be instantiated in any
larger universe in which the diagram is small.

Searches for an existing declaration: `msearch.py ... leanfinder "filtered colimits
preserve Joyal categorical equivalences of simplicial sets"` returned only generic
colimit existence, finite presentability, and monomorphism stability; no Joyal
stability theorem. `msearch.py ... loogle "categoricalEquivalence, colimit"` returned
zero hits (the unqualified identifier was unknown). `msearch.py ... grep
"Joyal|categoricalEquivalence|categorical_equivalence" AlgebraicTopology` returned
only `Mathlib/AlgebraicTopology/ModelCategory/JoyalTrick.lean`, whose abstract
lifting lemmas do not state filtered-colimit stability. `rg` over `lean/Sheaf` and
`WeilConjectures` found no existing theorem with this statement; the nearby
`FilteredColimitWeakHomotopyEquivalence` theorem concerns Kan weak homotopy
 equivalences and is a different notion. Therefore no existing declaration was
recorded and no new definition or dependency module was needed.

No `STATEMENT-DISPUTED` flag and no node fault.

Additional searches: `msearch.py ... leansearch "Filtered colimits of categorical
equivalences of simplicial sets are categorical equivalences"` returned filtered
colimit/finite-limit interchange, colimit comparison isomorphisms, and the eventual
equality description for set colimits; none states Joyal equivalence stability.
`msearch.py ... loogle '"Joyal", "colimit"'` reported service load, so that
query supplies no evidence of absence. A direct `rg` search for the proposed name
and the node id in the upstream project and side library found no declaration.
The nearby side theorem `exists_categorical_equivalences_small_generation` concerns
generation of the weak-equivalence class and does not assert closure under all
filtered colimits. The source supporting the node's proof was read online:
[Cisinski, Corollary 3.9.8](https://cisinski.app.uni-regensburg.de/CatLR.pdf),
printed pp.134--135, states precisely the filtered-colimit closure used here.
The separate worker will supply the independent second reading.

## Earlier second reading (a previous round; superseded)

Pending the separately dispatched second reader. This worker has not performed or
claimed an independent second reading. The second reader should check the model
parameterization, arbitrary filtered category, canonical colimit arrow, union
specialization, and independent testing-universe parameter against the node.

The full eleven-step DAG proof is included in the theorem docstring. The proof-only
imports include the stated interval-test module, the enhanced simplicial framework,
and Mathlib's nondegenerate-decomposition and relative skeletal-filtration modules.
No independent node is introduced and the item changes only in `lean`.

## Second reading by Q115

I reread the node statement and the complete theorem signature independently. The
objects and clauses match as follows:

* The node's simplicial sets and Joyal model structure are rendered by
  `M : HomotopicalAlgebra.ModelCategory SSet.{u}` and the explicit `hJoyal`
  equivalence characterization. This uses the dependency's weak-equivalence notion,
  with no private categorical-equivalence definition.
* The node's small filtered ordinary category is `(J : Type u)` with
  `[SmallCategory J] [IsFiltered J]`. `IsFiltered` supplies nonemptiness, common
  cocones for pairs, and eventual equalization of parallel arrows; no stronger
  directed-poset or injectivity assumption is present.
* The diagrams and natural transformation are exactly `(X Y : J ⥤ SSet.{u})` and
  `(a : X ⟶ Y)`.
* The objectwise hypothesis is exactly
  `ha : ∀ j : J, M.categoryWithWeakEquivalences.weakEquivalences (a.app j)`.
  The conclusion is exactly the same property for Mathlib's canonical
  `colimMap a`, which is the degreewise colimit map in `SSet`.
* The theorem is polymorphic in `u`; `v` occurs only in the dependency's testing
  universe `SSet.{max u v}`. Reinstantiation in a larger universe supplies the
  node's universe-enlargement clause. The filtered-union clause is the injective
  transition-map special case of this arbitrary filtered diagram statement.

I checked edge cases against both texts: `IsFiltered` excludes an empty index; the
  simplicial sets may be empty and may have only degree-zero simplices; `n = 0` is
  covered by the finite boundary argument in the proof docstring; transition maps
  need not be monomorphisms; non-posetal parallel arrows are handled by eventual
  equalization; and no characteristic, fibrancy, quasicategory, or finiteness
  hypothesis was added. The independent universe variables are bound explicitly
  (`u`, `v`) and no auto-implicit variable remains.

I searched Mathlib, `lean/Sheaf`, and `WeilConjectures` with LeanSearch,
Loogle/LeanFinder, and direct `rg` queries for filtered colimits, Joyal weak or
  categorical equivalences, and the theorem name. The hits were generic colimit
  facts, the Kan weak-homotopy filtered-colimit theorem, Joyal lifting lemmas, and
  small-generation results; none has this statement. The recorded dependency
  `SSet.exists_joyal_model_structure` was opened and its weak-equivalence clause
  matches `hJoyal` exactly. No new definition or dependency repair is needed.

No mismatch was found, so no Lean or node statement was changed. The retained
module compiles cleanly with `scompile.py`; its only proof hole is the named
statement theorem's `sorry`, and its declaration docstring includes all eleven
node proof steps, their source places, and `(blueprint:
lem-coef-joyal-filtered-equivalences)`.
