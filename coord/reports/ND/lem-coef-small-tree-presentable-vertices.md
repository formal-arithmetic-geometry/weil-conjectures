## Worker report

The module `Sheaf.CategoryTheory.SmallTreePresentableVertices` states
`CategoryTheory.CellularTree.smallTree_presentable_vertices_and_restrictions`, with one
`sorry` and no new definitions. Its two conclusions are presentability of every vertex
and of every downward-closed restricted colimit. No node correction or dependency repair
is needed; only the item's `lean` field changes. No repair note for this item was present.

Hypothesis and clause correspondence:

- The fixed small-set universe is `v`. The category is `{A : Type u} [Category.{v} A]`,
  with small Hom types and an independent object universe. All small colimits are
  `[HasColimitsOfSize.{v, v} A]`. No local presentability of `A` is added.
- The small cardinal is `(τ : Cardinal.{v})`; regularity is `[Fact τ.IsRegular]`,
  and uncountability is `(hτ : Cardinal.aleph0 < τ)`. Mathlib regularity is the
  infinite-cardinal/cofinality definition equivalent to the stated union condition.
- The preliminary definition of presentability is Mathlib's `IsCardinalPresentable`:
  the abbreviation expands to accessibility of `coyoneda.obj (op X)`, whose definition
  quantifies over every `SmallCategory` in `Type v` with `IsCardinalFiltered J τ`.
  That filteredness class requires cocones on every diagram with fewer than `τ` arrows,
  including empty diagrams. No separate filteredness hypothesis belongs on `T`.
- The arrow class is `(L : MorphismProperty A)` with no additional closure assumptions.
- The root is `(M : A) [IsCardinalPresentable M τ]`.
- The small well-founded poset is `(T : Type v) [PartialOrder T] [WellFoundedLT T]`;
  its size bound is `(hT : HasCardinalLT T τ)`, equivalent to `Cardinal.mk T < τ`.
- The specified L-tree is `(tree : CellularTree L M T)`. The existing structure includes
  its diagram into `Under M`, its specified cell arrows with membership in `L`,
  attaching maps, and pushout squares with the canonical predecessor leg.
- Endpoint presentability is exactly
  `(hcell : ∀ t : T, IsCardinalPresentable (tree.source t) τ ∧
  IsCardinalPresentable (tree.target t) τ)`. This is only imposed on the specified
  cells, not on every arrow in `L`.
- Every vertex is the first conclusion
  `∀ t : T, IsCardinalPresentable (tree.diagram.obj t).right τ`.
- Every downward-closed restricted colimit is the second conclusion
  `∀ E : Set T, IsLowerSet E →
  IsCardinalPresentable (subsetObj tree.diagram E).right τ`.
  `IsLowerSet` is downward closure for the inherited order, and `subsetObj` is precisely
  the chosen colimit of the restricted diagram in `Under M`, not the colimit in `A`
  obtained by forgetting the root.
- The stated particular cases are all instances of the second conclusion: `E = Set.Iio t`
  gives each predecessor object; `E = Set.univ` gives the total object; `E = ∅` gives the
  empty restriction. All three sets are lower sets. The notation `Y_∅ = M` means the
  canonical isomorphism already part of the dependency's colimit interpretation, not a
  literal equality of chosen objects. For the empty diagram the colimit is initial in
  `Under M`, hence canonically isomorphic to `Under.mk (𝟙 M)` and its underlying object
  to `M`. The empty restricted object is therefore included without replacing it by an
  arbitrary ordinary empty colimit (which would give the initial object of `A`).

Dependency declarations read and used:

- `def-coef-good-cellular-tree`: module `Sheaf.CategoryTheory.CellularTree`, declaration
  `CategoryTheory.CellularTree`, including its complete structure signature and fields;
  `CategoryTheory.CellularTree.subsetDiagram`, `.subsetObj`, `.predecessorMap` and `.IsGood`
  were also read. The statement uses `.subsetObj` and the structure fields directly.
- `def-weil-pbc-category-colimit`: module `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit`, its generated dual signature/docstring, and the cocone
  and canonical-map interface. It is imported publicly as the recorded dependency module.
- Proof dependency `lem-coef-ordinary-small-colimit-presentable` is a Mathlib leaf:
  `CategoryTheory.isCardinalPresentable_of_isColimit` in
  `Mathlib.CategoryTheory.Presentable.Limits`. Its full signature was read, including
  local smallness, the cardinal bound on `Arrow K`, and presentability of every value.
  That module is a non-public proof import. The cell and root cases are discharged by
  the proof plan, not substituted as added hypotheses about all vertices.

The declaration docstring carries all three DAG proof steps: adjoin the root to identify
restricted undercategory colimits with augmented ordinary colimits and bound their arrows;
induct on vertices using the small-colimit theorem and specified finite pushout spans;
then apply the same theorem to every lower restriction. It explains both finite/infinite
cardinal counts and the empty-predecessor case. No theorem was proved in this stage.

Source checked: [Lurie, Higher Topos Theory](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
Definition A.1.5.1 and Notation A.1.5.2, printed pp. 799-800 (PDF pp. 816-817 zero-based),
and Lemma A.1.5.11/Proposition A.1.5.12, printed pp. 806-809. The item is the
agent-formulated ordinary closure lemma, not a claim that HTT states this theorem verbatim.
The source's undercategory convention explicitly includes the empty restriction.

Edge cases checked before writing: empty `T` (vertex and cell quantifiers vacuous, the
only restriction gives the root); empty `E` in a nonempty tree; a minimal vertex (finite
pushout span rooted at `M`); a singleton tree; branching/incomparable vertices; a countable
well-founded tree at `τ = ℵ₁`; and a large category with small Hom sets (`u` independent
of `v`). None is excluded. `T` need not be directed, linearly ordered or nonempty. The
root need not be initial. There are no statement disputes.

Searches (through `msearch.py ND lem-coef-small-tree-presentable-vertices`, and direct rg):

- LeanFinder query: `A cellular tree on fewer than kappa vertices with presentable root
  and cell endpoints has presentable vertices and restricted colimits`.
  Eight hits: colimit-presentation/closure and ordinary small-colimit presentability
  theorems, presentability itself, and a factorization/equality theorem for presentables.
  No tree theorem: the small-colimit theorem assumes presentability of all values,
  whereas this item's vertices first require induction through the cell squares.
- LeanSearch query: `A well founded cellular tree with presentable root and fewer than
  kappa presentable cells has presentable vertices and all restricted colimits`.
  Eight hits, including `isCardinalPresentable_of_isColimit`, its primed form,
  `ColimitPresentation.isCardinalPresentable`, `IsCardinalLocallyPresentable.toHasColimitsOfSize`,
  and closure/accessibility declarations. None asserts this cellular-tree induction.
- Loogle initial query `CategoryTheory.IsCardinalPresentable, CategoryTheory.CellularTree`
  could not resolve the project-specific name. Corrected query
  `CategoryTheory.IsCardinalPresentable, CategoryTheory.IsPushout` succeeded with zero hits.
- Mathlib grep query `CellularTree|cellular.tree|isCardinalPresentable.*[Pp]ushout`,
  subdirectory `CategoryTheory`: zero hits. Read `Presentable/Basic.lean`,
  `Presentable/IsCardinalFiltered.lean`, `Presentable/Limits.lean`, and
  `SetTheory/Cardinal/HasCardinalLT.lean` for exact interfaces.
- Direct `rg -n 'CellularTree|cellular.tree|lem-coef-small-tree-presentable-vertices'`
  over upstream `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no upstream declaration or upstream blueprint-id match; project matches were the
  shared definition and distinct tree-presentation, approximation, enlargement and
  descent modules. Read the descent and approximation signatures: both assume local
  presentability and assert different constructions, so neither is this theorem.

Validation: the delivered module passed `scompile.py` with no errors or warnings
(sandbox pass 1.4 s; library-path pass 1.5 s). Every variable and universe is bound
explicitly, and `set_option autoImplicit false` is in the module. The node's Lean
signature is extracted verbatim from the source. Lines are at most 100 characters.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
