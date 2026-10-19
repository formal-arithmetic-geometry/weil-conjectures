## Worker report

The module `Sheaf.CategoryTheory.DiagramCellularCompatibleSlices` states
`CategoryTheory.CellularTree.diagram_cellular_compatible_slices` with `sorry`.
The three helper declarations spell out the canonical target map, slice, and
extension already defined in this node's statement. They introduce no independent
mathematical notion. All helper data are explicit, with no postponed theorem or
chosen arbitrary map. No DAG statement or dependency list changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The fixed small universe is `v`: Hom sets of `A`, the objects and morphisms of
  `D`, the tree indices, cardinal, and filtered-colimit shapes all use `v`.
  `A : Type u` permits a large category, without requiring `u = v`.
- `κ : Cardinal.{v}`, `[Fact κ.IsRegular]`, and `hκ : Cardinal.aleph0 < κ`
  express precisely uncountable regularity.
- `[IsCardinalLocallyPresentable A κ]` is Mathlib's cocompleteness plus a small
  family of presentable objects generating under small κ-filtered colimits.
  Its parent instance supplies the colimits needed by the shared tree interface.
- `{D : Type v} [SmallCategory D]` and `hD : HasCardinalLT
  (Σ d : D, Σ e : D, (d ⟶ e)) κ` bound the total set of morphisms, rather than
  merely individual Hom sets or the objects.
- `{F G : D ⥤ A} (f : F ⟶ G)` are arbitrary ordinary diagrams and their natural
  transformation, with all functoriality and naturality part of these types.
- `L : MorphismProperty A` and `hL` require presentable endpoints for every
  arrow in the specified class. `T`, its pointwise order and well-foundedness,
  `trees`, and `good` give the specified small κ-good cellular trees.
- `realization d` identifies the total tree colimit with `Under.mk (f.app d)`
  under `F.obj d`, exactly the root/total identification realizing the component.
  It is not a bare isomorphism that forgets the root map.
- `subsetObj` takes all restrictions in `Under (F.obj d)`, including empty
  restrictions. `diagramSliceTargetMap` is the shared canonical inclusion into
  the total restriction followed by the specified realization's hom.
- `DiagramSlice.lower` is downward closure. Its `map`, `map_id`, and `map_comp`
  give precisely a functor on these fixed objects. `root_naturality` makes the
  canonical root maps natural; `target_naturality` makes the canonical maps to
  `G` natural. Their composite is `f`: both the subset inclusion and realization
  are undercategory morphisms, so their root-commutation equations yield this
  equality. There are no independently chosen root or target maps.
- `A₀` and `M : DiagramSlice ... A₀` express an arbitrary prescribed slice,
  without a cardinal bound. `E` and `hE` are arbitrary κ-small seed subsets;
  downward closure is not imposed on the seeds.
- The conclusion quantifies `B`, `N : DiagramSlice ... B`, and
  `N' : DiagramSlice ... (fun d ↦ B d ∩ A₀ d)`. Its first conjunct is exactly
  `E d ⊆ B d` and `HasCardinalLT (B d) κ` for every `d`.
- The last two conjuncts are `IsDiagramSliceExtension ... N' N` and
  `IsDiagramSliceExtension ... N' M`, using respectively `inter_subset_left`
  and `inter_subset_right`. This predicate is the naturality square for the
  shared canonical `subsetMap`, not existence of an arbitrary transformation.
- There is no presentability assumption on `F.obj d`, `G.obj d`, or the
  restricted object on `A₀ d`. All cell endpoint conditions remain explicit.

Dependencies inspected and used:

- `def-coef-good-cellular-tree`: `Sheaf.CategoryTheory.CellularTree`, declarations
  `CategoryTheory.CellularTree`, `CellularTree.IsGood`, `subsetDiagram`,
  `subsetObj`, and `subsetMap`. Read the entire module, including its canonical
  predecessor-map construction and docstrings. The statement uses this exact
  interface rather than a private tree construction.
- `def-weil-pbc-category-colimit`: Mathlib
  `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`,
  `colimit.ι`, and `colimit.desc` (the chosen-colimit declarations are generated
  by `to_dual` from the displayed limit declarations). Read their signatures and
  docstrings; the tree's restricted objects and inclusions use these colimits.
- Proof import `Sheaf.CategoryTheory.SmallTreePresentableVertices` supplies
  `CategoryTheory.CellularTree.smallTree_presentable_vertices_and_restrictions`.
  Read its complete statement and proof docstring; the proof plan applies it in
  the undercategory with presentable initial root and free cell endpoints.
- The remaining proof imports are `Mathlib.CategoryTheory.Limits.Types.Filtered`
  for the elementwise filtered-colimit criteria and
  `Mathlib.SetTheory.Cardinal.Arithmetic` for the infinite-cardinal square bound.
  Every one of the node's eleven proof steps is included in the theorem docstring.

Edge cases checked before writing and on rereading:

Empty `D` and empty tree indices are allowed; the total-arrow type can be empty.
Empty restrictions use the shared undercategory colimit, hence the root, not an
initial object of `A`. The seeds may be empty or not downward closed. `A₀ d`
may be empty, the whole tree, or larger than κ. `B d ∩ A₀ d` is the literal
intersection. Nonmonic cells and nonmonic tree transitions are allowed; no
cancellation appears in the statement or proof plan. Nontrivial automorphisms
and all composable pairs are covered by the functor laws. Large, nonpresentable
roots and total objects are not excluded. No statement dispute or correction.

Searches performed:

- `msearch.py leanfinder`, query “Small cellular slices compatible with a
  prescribed diagram slice”: eight hits, on small-object attaching cells,
  relative cell complexes and orthogonal reflection; none states simultaneous
  natural slices and their prescribed intersections.
- `msearch.py loogle`, query `CategoryTheory.CellularTree,
  CategoryTheory.IsCardinalLocallyPresentable`: no hit (the custom tree identifier
  is not indexed by that search service). The actual local tree source was read.
- `msearch.py leansearch`, query “Small cellular slices of diagrams compatible
  with a prescribed slice and its intersections”: eight hits on partial
  sections, presheaf gluing and unrelated smallness instances; no match.
- `msearch.py grep`, regex `cellular.*slice|compatible.*slice|CellularTree` in
  Mathlib `CategoryTheory`: no match.
- Local `rg` of `CellularTree|cellular.*slice|compatible.*slice` in upstream
  `WeilConjectures` and side `lean/Sheaf/CategoryTheory` finds the shared tree
  and neighboring tree lemmas, but no compatible-diagram-slice theorem.
- Local `rg` of the four proposed declaration names in Mathlib, upstream, and
  side `lean/Sheaf`: no pre-existing declarations.
- Local `rg` of the item id in upstream: no occurrence.
- DAG search for cellular slices finds this ordinary node and the enriched
  analogue `lem-coef-enriched-cellular-compatible-slices`; its statement and
  empty Lean record were inspected. It has extra simplicial actions and does
  not already supply this ordinary statement. Other adjacent nodes concern
  projective cofibrancy or enriched pushout descent, not these slice data.

Source checked: opened the Harvard HTT PDF at printed pp. 879-882, the definition
of slices before A.3.3.15, the extension definition before A.3.3.16, and
A.3.3.16's intersection conclusion. The present node is its ordinary Set-enriched
specialization. Source link: https://people.math.harvard.edu/~lurie/papers/HTT.pdf

Validation uses the prescribed per-file `scompile.py` wrapper and `deliver2.py`
dry run; results are recorded below after completion.

Per-file validation: `scompile.py N4 lem-coef-diagram-cellular-compatible-slices`
compiled both the sandbox statement and its actual module path successfully,
with no errors or warnings. The delivered module contains one `sorry`, exactly
in the named theorem; definitions and structure data contain none.

## Second reading by N4

Independent maintainer second reading, 2026-10-17, of immutable delivery
`a8643366d959eaac0e9425ba590f2231d5fe86fc`. This reviewer did not author the
module or the preceding worker report. The original section contained only a
placeholder; this complete replacement supplies the required substantive reading.

I read the item, both statement-dependency records, the actual declarations in
`CellularTree.lean`, the proof dependency `SmallTreePresentableVertices.lean`,
and the Mathlib declarations used for colimits, presentability, filteredness,
elementwise colimits and cardinal arithmetic. I read HTT A.3.3.15-16 and the
preceding slice/extension definitions, printed pp. 879-882 (PDF pages 896-899,
zero-based), and A.1.5.1-2, printed pp. 799-800. Source:
https://people.math.harvard.edu/~lurie/papers/HTT.pdf . I also read Stacks
`categories.tex`, `definition-colimit` and `definition-directed`.

Hypothesis and conclusion audit (all match):

- `A : Type u`, `Category.{v} A` gives an ordinary category with small Hom sets.
  `v` is the fixed small universe; `u` is independent. `Cardinal.{v}`,
  `Fact κ.IsRegular` and `aleph0 < κ` give precisely uncountable regularity.
- Mathlib `IsCardinalLocallyPresentable A κ` extends
  `HasCardinalFilteredGenerator A κ` and `HasColimitsOfSize.{v,v} A`.
  The generator is essentially small, equivalently representable by a small
  family, and consists of presentable objects generating by the stated
  filtered colimits. `IsCardinalPresentable` means accessibility of coyoneda;
  `IsCardinalFiltered` tests diagrams whose total arrow type has size below κ.
  These are the node's definitions, with no additional assumption on the root.
- `D : Type v`, `SmallCategory D`, and `hD` bound the total type
  `Σ d, Σ e, (d ⟶ e)`, not just individual Hom sets. Empty D is permitted.
  `F G : D ⥤ A` and `f : F ⟶ G` are the prescribed ordinary diagrams and map.
- `L` and `hL` require presentable endpoints for every attaching arrow in L.
  `T`, its pointwise partial orders and well-foundedness, `trees`, and `good`
  use the shared `CellularTree` and `IsGood` exactly. Goodness bounds cell
  endpoints and strict predecessor sets; it does not bound roots or vertices.
- `realization` is an isomorphism in `Under (F.obj d)` from the full tree
  colimit to `Under.mk (f.app d)`. Thus it realizes the given arrow, including
  the root map. All restrictions use the shared `subsetObj` in this same
  undercategory; `subsetMap` is the colimit-induced inclusion map.
- `diagramSliceTargetMap` really is `subsetMap` into the full tree followed
  by the specified realization. Its composite with the canonical root map
  is f by the two undercategory commutation equations. It is not arbitrary.
- `DiagramSlice.lower`, `map`, `map_id`, `map_comp` are precisely downward
  closure and functorial arrows. `root_naturality` and `target_naturality`
  make the two canonical transformations natural. Bundling the laws in a
  structure rather than a Functor adds no hypothesis or choice restriction.
- `A₀` and `M` impose no cardinal bound on the prescribed slice. `E`, `hE`
  impose only size on seeds, not downward closure.
- The existential B and structures N and N' have exactly B and literal
  intersections `B d ∩ A₀ d`. The first conjunct requires seed containment
  and cardinality below κ at each object. The two extension conjuncts use
  `Set.inter_subset_left/right` and the shared canonical `subsetMap`.
  Expanding `IsDiagramSliceExtension` gives precisely naturality of these
  two canonical intersection maps. No monicity or cancellation is assumed.

The proof docstring contains all eleven node steps. Steps 1-2 establish
presentability relative to the root, using free endpoints `R ⟶ R ⨿ P` and
initial root `1_R` in the undercategory before applying the existing small-tree
theorem. That theorem's hypotheses include the presentable root, small indexing
set and presentable cell endpoints; all are supplied in that application.
Step 3 presents G and M by filtered unions of small restrictions, including
on tails. Step 4 uses exactly the elementwise existence and eventual-equality
clauses; total arrows bound the number of identity, composition and transition
requirements. Steps 5-8 give typed successive partial maps, with equality
witnesses in G or M. In particular intersection equality is witnessed in G,
not inferred by cancelling its structure map. Enlargements postcompose both
sides, including the composition comparisons with the preceding maps fixed.
Steps 9-11 take the countable unions, use uncountable regularity for size, and
check identities, compositions, both structural transformations and both
intersection maps on colimit legs. The elementary steps are universal-property
and cardinal-union calculations; no unrecorded non-elementary prerequisite
or additional helper theorem is needed to state this result.

Edge cases: empty D; empty T; empty seeds and seeds not downward closed;
empty intersections; A₀ equal to the whole tree or arbitrarily large;
branching well-founded posets; nontrivial automorphisms in D; nonmonic cells;
and roots, totals and prescribed-slice objects that are not presentable.
In particular the empty restricted colimit is the root, not an initial object
of A. All these cases remain admitted. There is no universe equality u=v,
no extra size bound on A, and no pro-etale replacement of an ordinary category.

Independent duplicate searches used different terms: `cellular.?tree`,
`good.?tree`, `tree.?slice`, `slice.?extension` in pinned Mathlib,
WeilConjectures and the side category-theory modules, plus all four delivered
names. No existing equivalent slice structure or theorem was found.
`RelativeCellComplex/Basic.lean:40-59` instead requires a linear well-order and
successor attachments. LeanSearch query "Small downward closed cellular
subdiagrams admitting functorial maps and natural intersection inclusions"
returned directed-category constructions and Type-valued subfunctors, not this
result. Loogle query `"IsCardinalPresentable", "Under"` returned four general
closure/retract declarations, not the theorem or helper notions. The enriched
cellular-compatible-slices DAG node has additional simplicial actions and no
recorded Lean declaration; it is not a duplicate usable here. The worker also
records all three required kinds of search. Existing tree/colimit notions are
reused, not redefined.

Mechanical checks: the JSON `lean.statement` equals the file's complete
signature verbatim up to `:= by`; every delivered declaration is listed in
`lean.declarations`. The module and all four declarations have source-place
and blueprint docstrings. No line exceeds 100 characters. There is exactly one
`sorry`, the main theorem's entire proof. The target-map definition has actual
canonical data, the extension definition is an explicit equation, and the slice
structure has actual fields. No local proof, local notation or local instance
was added. There are no new nodes, dependency-module repairs, or statement
corrections, so a §1(C) citer audit is inapplicable.

Reproduced per-file validation with the prescribed command:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py N4 lem-coef-diagram-cellular-compatible-slices <immutable snapshot module path>`

The installed wrapper currently confirms compilation on the server using the
side overlay. It returned exit 0, no errors or warnings, and reported:

- sandbox `Sheaf/Stage2/Sandbox0.lean`: 1.4 seconds;
- library `Sheaf/CategoryTheory/DiagramCellularCompatibleSlices.lean`: 1.8 seconds;
- private compiled imports under `/dev/shm/nt-tmp/nt-local-compile-chz5spj7/.lbuild`.

This reproduces the worker's recorded per-file result. No global build, live
Lean edit, direct SSH command, repository mutation or delivery command was run.

Finding and correction: H1/H11, the original second-reading section was only a
placeholder. This report replacement supplies the independent clause-by-clause
reading. The mathematics, module and node record require no changes.
