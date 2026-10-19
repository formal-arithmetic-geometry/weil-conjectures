## Worker report

The module `Sheaf.CategoryTheory.DirectedDecompositionRightAnodyne` states
`SSet.Enhanced.rightAnodyneExtensions_directedDecompositionNerveInclusion`.
It constructs the decomposition simplicial set and its canonical pure-base and
pure-nerve inclusions as helpers belonging to this node. The only postponed theorem
is the main statement, with proof `sorry`; its docstring gives the source proof.
There are no hollow definitions, additional theorem assumptions, or statement corrections.

Hypothesis and clause correspondence:

- Small simplicial sets: `(K : SSet.{u})`, using the existing Mathlib simplicial sets
  and the universe conventions imported by `EnhancedDiagramsCones`. The universe `u`
  is explicit, arbitrary, and shared with the small index set.
- Small nonempty partially ordered set: `(I : Type u) [PartialOrder I] [Nonempty I]`.
- Every finite subset has an upper bound: `hI : ∀ s : Finset I, ∃ b : I,
  ∀ a ∈ s, a ≤ b`. This includes the empty finite subset.
- Simplicial subsets: `B : I → K.Subcomplex`, using Mathlib's actual subfunctors.
- Increasing subsets: `hB : Monotone B`.
- Their union is all of `K`: `hcover : iSup B = ⊤`; subcomplex suprema are computed
  degree by degree, so this includes degenerate as well as nondegenerate simplices.
- The node's explicitly defined `K_F` is `directedDecomposition K B`, the underlying
  simplicial set of `directedDecompositionSubcomplex K B`. Its ambient object is the
  existing ordered join `orderedJoinFunctor.obj (K, nerve I)`. Its subcomplex is the
  union of the pure-left and pure-right ranges and, for each `a`, the range of the
  join map `(B a).toSSet ⋆ nerve {b // a ≤ b} → K ⋆ nerve I`. The upper map is
  `decompositionUpperInclusion a`, obtained by applying `nerveMap` to the actual
  monotone subtype inclusion.
- Degreewise identification with the displayed disjoint-union formula: join normal
  forms have a unique cut into possibly empty consecutive blocks. Both nonempty
  blocks give `σ ∈ K_i` and a chain `b₀ ≤ ⋯ ≤ bⱼ`, with `i+j+1=n`. Membership in
  our union means that some `a ≤ b₀` satisfies `σ ∈ B a`. By `hB` this is equivalent
  to `σ ∈ B b₀`; conversely choose `a=b₀`. Thus there is exactly one copy of the
  specified mixed simplex for each cut, initial simplex and final chain. The pure
  factors give exactly `K_n` and `N(I)_n`. Ranges and suprema are subsets of the
  ambient join, so overlaps never introduce additional copies.
- Operators: the subcomplex inherits the ordered-join operators. They restrict or
  repeat the two consecutive blocks. Deleting the first upper index changes the
  membership from `B b₀` to `B b₁` by monotonicity. Losing all upper vertices retains
  the initial simplex in `K`; losing all lower vertices retains the nerve chain.
  This is exactly the node's convention, including degeneracies and pure blocks.
- Pure inclusions: `directedDecompositionBaseInclusion K B` and
  `directedDecompositionNerveInclusion K B` factor `orderedJoinInl` and
  `orderedJoinInr` through the union containing their ranges, using Mathlib's
  `Subcomplex.lift`. The structural lattice proofs specify the factorization;
  no filler, arbitrary map, or existence-choice enters these definitions.
- Conclusion: `rightAnodyneExtensions (directedDecompositionNerveInclusion K B)`.
  This is exactly the recorded right-anodyne property, with positive-index horns,
  isomorphisms, pushouts, transfinite compositions and retracts.
- Neither `K` nor any `B a` has a `Quasicategory` binder. There are no cone data.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: the existing simplicial and ordinary
  nerve conventions (`CategoryTheory.nerve` in Mathlib); its recorded `coneCategory`
  signature and docstring were read, but no cone structure is used in this theorem.
- `Sheaf.CategoryTheory.RightAnodyne`: `SSet.rightAnodyneExtensions`, read in full,
  is the conclusion's morphism property. Its generating horn condition is `0 < i`
  for `i : Fin (n+1)`, so it automatically excludes degree zero and includes `i=n`.
- `Sheaf.CategoryTheory.JoinSliceRightFibration`: the existing
  `SSet.Enhanced.orderedJoinInl` and `orderedJoinInr`, read with their definitions
  and docstrings. This landed node `lem-coef-infinity-slice-right-fibration` was
  added to `stmt_deps` because these canonical maps implement the decomposition.
  The slice theorem itself is not used or assumed. Its signature/docstring was
  also read; importing a theorem module does not impose its theorem hypotheses.
- That module publicly imports `Sheaf.AlgebraicTopology.PushoutJoinSaturation`,
  which supplies `SSet.Enhanced.orderedJoinFunctor`; its full definition/docstring
  was read. It is the existing Day convolution of terminal augmentations along
  ordinal concatenation, whose documented normal forms are the precise ordered
  join formula. This delivery does not define a second join.
- Mathlib `SSet.Subcomplex.range`, `Subcomplex.lift`, `Subcomplex.toSSet`, supremum
  lattice operations, `OrderHom.Subtype.val`, and `CategoryTheory.nerveMap` supply
  the concrete construction. Their source definitions were inspected.

Source verification: downloaded and read Lurie's HTT PDF, specifically Notation
the project server and Remark the project server (pp. 248--249), Proposition the project server and Remark the project server
(pp. 252--253). The latter explicitly specializes to monotone simplicial subsets
and says directedness plus the union condition suffices. Thus the node needs no
correction. The proof docstring explains nonempty directed simplex-index posets,
the degenerate-lift equality for subcomplexes, and the source's attachment argument.

Edge cases checked:

- Empty `K`: all `B a` are empty, there are no mixed or pure-base simplices, and
  `K_F` is the pure nerve; its inclusion is an isomorphism, hence right anodyne.
- Singleton `I`: the cover forces its one subset to equal `K`; the decomposition
  is the usual right cone and the nerve map is the final-vertex inclusion.
- Empty covering subsets are permitted. For any actual ambient simplex the cover
  gives a nonempty index poset, and directedness plus monotonicity gives its finite
  upper bounds. No individual subset is assumed nonempty or to be a quasicategory.
- The empty finite subset in `hI` is retained. Dimension zero consists of exactly
  the disjoint pure vertices, since no mixed cut exists. Higher degeneracies are
  retained by the ambient join and the subcomplex operations.
- Distinct indices with identical subsets remain distinct nerve vertices. Join
  range union identifies only equal ambient mixed simplices, as required.

Searches for an existing statement/construction:

- `msearch.py ... leanfinder`: "The nerve inclusion into the simplicial decomposition
  of an increasing directed cover is right anodyne". Eight hits including
  `SSet.modelCategoryQuillen.J`, `.I`, `.horn_ι_mem_J`, nerve Segal results, and
  simplicial thickening. None is the directed decomposition statement.
- `msearch.py ... loogle`: `"anodyne", "nerve"`. Zero hits, on both runs.
- `msearch.py ... leansearch`: "Directed cover of simplicial subsets nerve inclusion
  decomposition right anodyne". Eight hits, including truncated right extension,
  directed affine covers, Quillen generating horns and the nerve quasicategory
  instance. No match.
- `msearch.py ... grep`: `right.?anodyne|decomposition|directed` in
  `AlgebraicTopology/SimplicialSet`. Five hits: ordinary paths, nondegenerate-simplex
  decompositions and `HomotopyCat`; no right-anodyne decomposition theorem.
- `rg` of the upstream `WeilConjectures` tree for `decomposition`, directed-cover
  names, right-anodyne names and the exact item ID found no relevant statement.
  A second exact-name search for all new construction stems in Mathlib, upstream,
  and `lean/Sheaf` found no collisions.
- `rg` of `lean/Sheaf/CategoryTheory` found the reusable ordered join in
  `PushoutJoinSaturation`, its pure inclusions in `JoinSliceRightFibration`, and
  the consumer `InfinityDirectedConeCover`, whose proof mentions this currently
  missing decomposition theorem but does not define it. Those source files were
  read. The new helpers implement the construction already introduced by this
  item's own statement, rather than adding an independent mathematical notion.
- `rg` of DAG nodes for `K_F`, "directed simplicial" and "decomposition simplicial"
  found this item and its consumers, with no existing definition node for this
  construction. The new dependency was checked for a path back to this item;
  there is none, so it does not create a dependency cycle.

Validation: the final delivered module was checked with the prescribed
`scompile.py NW lem-coef-directed-decomposition-right-anodyne <file>` wrapper.
Both its sandbox and library-module checks passed with no errors or warnings.

Continuation audit (2026-10-17): reopened the node and all three statement-dependency
records, the actual `RightAnodyne`, `EnhancedDiagramsCones`, `JoinSliceRightFibration`
and `PushoutJoinSaturation` declarations, and the archived HTT Notation the project server,
Proposition the project server and Remark the project server. Repeated LeanFinder, Loogle, LeanSearch and
Mathlib grep searches; none gives the statement. Loogle again returns zero hits;
LeanFinder and LeanSearch give ordinary nerve, Quillen horn-generator and unrelated
cover results. Exact helper-name searches find no collisions in Mathlib, upstream or
the project's library. The original construction and theorem signature are retained.

Added non-public proof imports `Sheaf.CategoryTheory.FilteredNerveWeakContractibility`
(`CategoryTheory.isContractible_nerve_of_isFiltered`, with its dual) and
`Mathlib.AlgebraicTopology.SimplicialSet.Skeleton`
(`SSet.relativeCellComplexOfMono`, also exposing `SSet.exists_nonDegenerate`,
`SSet.unique_nonDegenerate_dim`, `SSet.unique_nonDegenerate_simplex`, and
`SSet.unique_nonDegenerate_map`). The recorded sources and docstrings were read.
`lem-coef-contractible-join-right-anodyne` has neither a Lean record nor a Mathlib
match on the base, so its proof import is omitted until it is stated; its statement
is not needed to type this delivery. The proof docstring now follows all four DAG
proof steps explicitly, using only nondegenerate roots and the corresponding join
attachments. No theorem was proved. The node copy differs from the base only in
`lean` and the added landed statement dependency; its Lean record date is refreshed.

## Second reading by NW

I independently reread the node, the HTT source, the dependency declarations, and the Lean file.
The node's objects, hypotheses, and conclusion match as follows:

- The small simplicial set is `K : SSet.{u}`. The Lean universe is explicit and the same
  universe is used for the small index type, as in the project's simplicial-set size convention.
- The small nonempty poset is `I : Type u` with `[PartialOrder I]` and `[Nonempty I]`.
  The finite-upper-bound hypothesis is exactly
  `hI : ∀ s : Finset I, ∃ b, ∀ a ∈ s, a ≤ b`; it includes the empty finite set.
- The family of simplicial subsets is `B : I → K.Subcomplex`, with the source's
  order-preservation rendered by `hB : Monotone B`, and the cover by `hcover : iSup B = ⊤`.
- The displayed `K_F` is rendered by `directedDecomposition K B`, whose ambient object is
  the existing `orderedJoinFunctor.obj (K, nerve I)`. Its subcomplex is the supremum of the
  pure-left range, pure-right range, and the ranges of
  `orderedJoinFunctor.map (((B a).ι, decompositionUpperInclusion a))` for all `a`.
  `decompositionUpperInclusion` is the canonical nerve map from the subtype `a ≤ b`.
- The ordered-join normal form gives the pure `K` and pure `N(I)` summands and one mixed
  summand for each cut. Monotonicity makes membership through some `a ≤ b₀` equivalent to
  membership in `B b₀`, so the subcomplex has exactly the node's mixed formula and its face
  and degeneracy rules. The two maps
  `directedDecompositionBaseInclusion` and `directedDecompositionNerveInclusion` are the
  canonical pure-factor inclusions factored through that subcomplex.
- The conclusion is exactly
  `rightAnodyneExtensions (directedDecompositionNerveInclusion K B)`, with the existing
  right-anodyne definition supplying isomorphisms, positive-index horns, pushouts,
  transfinite compositions, and retracts.

The HTT reading (Notation the project server, Proposition the project server, and Remark the project server, pp. 248--253)
confirms that no quasicategory, cone, or Kan hypothesis is present. The source's directed
poset condition is represented by the stated finite-upper-bound condition. Edge cases checked
were empty `K`, empty individual `B a`, a singleton index poset, duplicate subsets at distinct
indices, the empty finite subset in `hI`, dimension zero, and degenerate lower simplices.
The construction handles all of them: the empty `K` case leaves the pure nerve, dimension zero
has only the pure factors, and degeneracies are inherited from the ambient join.

I reread the declarations used by the file: `SSet.rightAnodyneExtensions` in
`Sheaf.CategoryTheory.RightAnodyne`; `SSet.Enhanced.orderedJoinFunctor` in
`Sheaf.AlgebraicTopology.PushoutJoinSaturation`; and the canonical
`orderedJoinInl`/`orderedJoinInr` in `Sheaf.CategoryTheory.JoinSliceRightFibration`.
The latter is the landed statement dependency added in the worker copy; it supplies the
canonical maps used by the helper inclusions and does not add a theorem hypothesis. I also
checked the Mathlib `Subcomplex.range`, `Subcomplex.lift`, `Subcomplex.toSSet`, `iSup`, and
`CategoryTheory.nerveMap` declarations, plus the filtered-nerve and nondegenerate-decomposition
proof imports. LeanSearch, LeanFinder, Loogle, and pinned Mathlib/upstream/project grep found
no existing directed-cover right-anodyne statement or duplicate helper construction.

No mismatch was found. I made no Lean or node correction; the worker's canonical ordered-join
construction, theorem signature, and `sorry`-only proof are retained. The only delivery metadata
change is the recorded landed join-inclusion dependency already present in the sandbox node copy.
