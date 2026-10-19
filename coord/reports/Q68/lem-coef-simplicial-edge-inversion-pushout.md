## Worker report

The module `Sheaf.CategoryTheory.SimplicialEdgeInversionPushout` defines the two edge maps from
`Δ[1]` to `Δ[3]`, their coproduct collapse to two separate `Δ[0]` summands, and the pushout
`inverseGadget` representing the quotient Q in the node. It defines `inverseGadgetEdge` as the
image of the edge 12, then defines the coproduct attaching maps for a set `W` of edges of `C`,
the degreewise simplicial-set pushout `edgeInversionPushout C W`, and its canonical map.
The theorem `edgeInversionPushout_isLocalization` states
`IsLocalizationAtEdges (edgeInversionPushoutMap C W) W`.

The binders `(C : SSet.{u})` and `(W : Set (C _⦋1⦌))` render the node's arbitrary small
simplicial set and arbitrary collection of edges. The `inverseGadgetEdges` map uses the two
standard simplex edges 02 and 13, while `inverseGadgetCollapse` sends each interval to its own
coproduct point, so the pushout is exactly the displayed quotient Q and keeps the two collapsed
vertices distinct. `inverseGadgetEdge` is the image of edge 12. `edgeInversionAttachingMap`
represents each `w : W` by `yonedaEquiv.symm w.1`; `edgeInversionGadgetMap` attaches one copy of
Q along each such representative, including degenerate edges. The final theorem uses the recorded
`IsLocalizationAtEdges` predicate, whose definition quantifies over every quasicategory test
object in the containing universe, gives a simplicial restriction factorization through the full
edge-inverting subcategory, and requires a coherent functor equivalence. No quasicategory
hypothesis is added on `C` or on the pushout.

Dependency declarations used:

- `SSet.Enhanced.IsLocalizationAtEdges` from `Sheaf.CategoryTheory.UniversallyLocalizingSimplicialMap`.
- The simplicial-set and functor constructions from `SSet.Enhanced` in
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`.
- Proof-plan imports (non-public, stages/2-statements.md §3 rule 7) are the modules of
  `SSet.Enhanced.mapping_composition`, `SSet.Enhanced.enhanced_functor_cone_calculus` and
  `SSet.Enhanced.pointwise_equivalences`. The proof nodes
  `lem-coef-inverse-gadget-categorical-contractibility` and
  `lem-coef-localization-monomorphic-pushout` have no landed Lean declaration, so they are
  neither imported nor restated in this stage-2 statement module.

Edge cases checked: `W = ∅` gives coproducts indexed by the empty subtype and the terminal
(empty-product) attachment; a degenerate edge is still represented by `yonedaEquiv.symm w.1`;
distinct selected edges sharing endpoints get separate gadget copies because the index is the
subtype `W`; and the two quotient points are separate Bool summands. The definitions use Mathlib's
presheaf `pushout` and `Sigma` coproducts degreewise, so no nonempty or quasicategory assumption
is hidden.

Searches made for duplicate notions: `msearch.py ... leanfinder "Pushout adjoining finite inverse gadgets to edges localizes a simplicial set"` returned only generic
Mathlib horn/model-category declarations and no match; `msearch.py ... loogle '"SSet", "IsLocalization"'` returned 0 hits; `msearch.py ... grep 'localiz.*simplic|simplic.*localiz|inverseGadget|edgeInversion' AlgebraicTopology` returned 0 hits; additional LeanSearch and LeanFinder searches for simplicial localization and the 02/13 quotient returned only generic localization, horn, and standard-simplex declarations. `rg` over the project and source found no declaration for this node. The source search at Kerodon tags 05ZJ, 05ZK, and 05ZL confirms the quotient Q, edge 12, and pushout localization statement.

No `STATEMENT-DISPUTED` flag or node fault. The file compiles cleanly with `scompile.py`.

## Second reading by Q68

The group did not run a separate second reading (its dispatched brief required direct
delivery). This section records the full reading made in the maintainer's review of
delivery 163a2ac4 (reviewer service, 2026-10-17), against the node, Kerodon 05ZJ/05ZK/05ZL
as recorded in the node, and the compiled module.

Node statement, item by item, with its Lean rendering and verdict:

1. $Q=\Delta^3\amalg_{\Delta^{\{0,2\}}\amalg\Delta^{\{1,3\}}}(\Delta^0\amalg\Delta^0)$, each
   edge collapsed to its own point. `inverseGadgetEdges` is `Sigma.desc` over `Bool` of
   `yonedaEquiv.symm (stdSimplex.edge 3 0 2 _)` (false) and `stdSimplex.edge 3 1 3 _` (true);
   `inverseGadgetCollapse` sends summand `b` to the terminal map followed by `Sigma.ι _ b`,
   so the two points stay distinct; `inverseGadget` is the presheaf `pushout` of the two,
   computed degreewise. Correct.
2. $e:\Delta^1\to Q$, image of edge $\{1,2\}$, oriented $1\to2$ (endpoints to $B,A$).
   `inverseGadgetEdge = yonedaEquiv.symm (stdSimplex.edge 3 1 2 _) ≫ pushout.inl _ _`.
   Correct.
3. Arbitrary small $C$ and arbitrary $W\subseteq C_1$: binders `(C : SSet.{u})`,
   `(W : Set (C _⦋1⦌))`; no quasicategory, finiteness or nondegeneracy hypothesis. Correct.
4. Each $w$ as its representing map $\Delta^1\to C$: `edgeInversionAttachingMap` is
   `Sigma.desc (fun w ↦ yonedaEquiv.symm w.val)` over the subtype `W`. Correct.
5. $D=C\amalg_{\coprod_W\Delta^1}\coprod_W Q$ along $\coprod e$: `edgeInversionGadgetMap`
   is `Sigma.desc (fun w ↦ inverseGadgetEdge ≫ Sigma.ι _ w)`; `edgeInversionPushout` is the
   presheaf pushout of the two legs. Correct.
6. $j:C\to D$ canonical: `edgeInversionPushoutMap = pushout.inl _ _`. Correct.
7. Conclusion: for every quasicategory $E$, $j^*$ factors through the $W$-inverting full
   subcategory and is a coherent functor equivalence onto it.
   `IsLocalizationAtEdges.{u, v} (edgeInversionPushoutMap C W) W`, the recorded declaration of
   the stmt_dep `def-coef-universally-localizing-simplicial-map`: for all
   `E : SSet.{max u v}` with `Quasicategory E`, there is `r` with
   `r ≫ (edgeInvertingDiagrams C W E).ι = (MonoidalClosed.pre (uliftFunctor.map j)).app E`
   and `IsFunctorEquivalence r`. Same quantifier order, neither weaker nor stronger; `v` is
   free, so test quasicategories in every containing universe are covered. Correct.
8. "Neither $C$ nor $D$ is assumed to be a quasicategory": no such hypothesis. Correct.

Edge cases: `W = ∅` (empty coproducts, `D ≅ C`) included; `C` empty forces `W = ∅`,
included; degenerate edges of `W` are represented by `yonedaEquiv.symm` and get their own
gadget; distinct edges sharing endpoints get separate gadget copies since the index is the
subtype `W`; every universe `u` of `C` and every test universe `max u v` is allowed.

Searches: `rg` for `inverseGadget|edgeInversion` over the project's `lean/` and the source
repository found no other declaration of these names. `rg` for `edge 3 0 2` / 05ZJ found
`SSet.Enhanced.inverseTetrahedron` and `inverseTetrahedronCentralEdge` in
`Sheaf.AlgebraicTopology.FiniteInverseTetrahedron` (node `lem-coef-finite-inverse-tetrahedron`,
HA B.1.6), an isomorphic presentation of the same $Q$ by two successive pushouts with the same
central edge `12`. That node is not in this item's stmt_deps or proof_deps, and the item
statement writes $Q$ out itself, so the item's helpers render its own data; the two
presentations should be identified by an isomorphism when either is proved (noted for the
lead, no change here).

Mismatches found: none in the Lean. Changes: the worker report's sentence on proof-plan
imports was garbled and was rewritten; this section replaces the group's placeholder.
Compile: `tools/nt_compile.py` on the delivered file, rc 0, no error and no warning.
