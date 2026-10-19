## Worker report

The module `lean/Sheaf/AlgebraicTopology/MarkedActionEdgeComparison.lean` defines
`SSet.Marked.intervalDiagonal`, the simplicial diagonal of the interval used to pair
parameter and acted-on edges, and states
`SSet.Marked.marked_action_edge_comparison` with proof `sorry`.

The theorem uses `A : SSet`, marked simplicial sets `Y` and `X`, a marked map
`μ : Marked.product (Marked.sharp A) Y ⟶ X`, a quasicategory `Z`, a simplicial map
`h : X.underlying ⟶ Z`, and the hypothesis `hh` that every edge in `X.marking` maps
under `h` to an `Enhanced.IsEquivalenceEdge`. The first conjunct quantifies every
edge `e : Δ[1] ⟶ Y.underlying` and parameter edge `g : Δ[1] ⟶ A`; it states the
if-and-only-if between the equivalence of the paired action edge
`h ∘ μ ∘ (g,e)` and the equivalence of the same edge with `g` replaced by the
constant edge at `g(0)`. The pairing is rendered by `intervalDiagonal`,
`g ⊗ₘ e`, and `μ.val`, and the resulting edge is extracted with
`SSet.yonedaEquiv`. The second conjunct quantifies an arbitrary acted-on edge `e`,
assumes for every vertex `a : A _⦋0⦌` that the constant action edge is an equivalence,
and concludes the same for every parameter edge `g`. No marking condition on `e`
and no Kan assumptions on `A`, `Y.underlying`, or `X.underlying` are present.

The dependency declarations used are:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
  `SSet.Enhanced.IsEquivalenceEdge` (equivalence-edge predicate and simplicial-set
  primitives).
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`,
  `SSet.Marked`, `SSet.Marked.Hom`, `SSet.Marked.sharp`, and
  `SSet.Marked.product` (marked sets, sharp marking, products, and maps).
- `Sheaf.CategoryTheory.InfinityMappingComposition`,
  `SSet.Enhanced.mapping_composition` (the mapping-composition theorem used by the
  postponed proof).

The edge cases checked before writing the statement were: a degenerate `g`, a
constant/degenerate `e`, a zero-dimensional parameter simplicial set (the universal
edge assertion is then vacuous), empty `A`, empty underlying marked sets, and the
absence of any marking on `e`. The diagonal is defined by Yoneda from the pair of
identity 1-simplices, so it is available even in the degenerate interval case.

Searches made before writing:

- `msearch.py Q11 lem-coef-marked-action-edge-comparison leanfinder` for marked
  action edge comparison and for simplicial squares with equivalence sides: only
  generic `SSet.Edge`/horn hits; no matching theorem.
- `msearch.py ... loogle` with `"SSet", "Marked"` and `"MarkedSSet"`: no hits.
- `msearch.py ... grep` for marked action/equivalence-square patterns in
  `AlgebraicTopology`: no relevant hits; unrelated Mathlib hits were discarded.
- `rg` over `WeilConjectures` and `lean/Sheaf` for marked action, edge comparison,
  and `MarkedSSet`: no existing declaration with this statement.
- The recorded declarations and full docstrings of all three statement dependencies
  were read. None states this comparison, so no duplicate definition exists.

## Second reading by Q11

I reread the node statement and the module signature clause by clause. The binders
`A`, `Y`, `X`, `μ`, `Z`, `h`, and `hh` are exactly the node's small simplicial set,
marked sets, marked action, quasicategory, map, and marking-to-equivalence hypothesis.
The first universal clause binds exactly `e` and `g`; its left edge is the node's
`g^*e`, rendered as `intervalDiagonal ≫ (g ⊗ₘ e) ≫ μ.val`, and its right edge is
the node's `g(0)^*e`, rendered with `SSet.const` at
`g.app _ (stdSimplex.obj₀Equiv.symm 0)`. The predicate on both sides is exactly
`Enhanced.IsEquivalenceEdge Z` after applying `h`. The second clause has exactly the
node's universal vertex assumption and universal edge conclusion. No marking
hypothesis on `e`, Kan hypothesis, or extra conclusion was introduced. The helper
`intervalDiagonal` is the canonical pointwise pairing map and does not alter the
objects or hypotheses in the theorem.
