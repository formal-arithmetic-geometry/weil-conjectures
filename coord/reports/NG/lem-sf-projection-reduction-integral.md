## Worker report

The item is already stated exactly by
`WeilConjectures.sixFunctorProjection_reduction_integral` in
`Sheaf.Paper.ProjectionFormulaCoherence`. I therefore added no module and attached the
node to that existing declaration with `existing: true`. Its proof remains `sorry`, as
required for a stage-2 statement; no definition or theorem was redefined.

The source declaration was read in full. Its signature renders every part of the node:
`S : SixFunctorDatum D C E n hn` supplies the fixed finite-field, coefficient, and
six-functor datum; `f : X ⟶ Y` with `[IsSeparated f.hom.left]` is the separated
finite-type morphism; `c : Compactification f.hom.left` supplies the open/proper
factorization; `K` is an integral constructible object on `X`; `L` and arbitrary `N`
are integral constructible objects on `Y`; and the conclusion is precisely
`sixFunctorProjectionIntegralReductionSquare S f c K L N`. The definition of that
square in the same module contains the normalized integral tensors, compact-support
projection components, associators, and pullback tensor comparison in exactly the
displayed equation of the node. It imposes no finite-Tor restriction on `K`, `L`, or
`N` beyond membership in the stated integral constructible category. Its definition
also retains the constant-quotient specialization and the zero and unit cases.

Dependency declarations read:

- `WeilConjectures.SixFunctorDatum` from `Sheaf.Paper.SixFunctorDatum` (the six-functor
  structure extending the operation datum).
- `WeilConjectures.SixFunctorOperationDatum` from
  `Sheaf.Paper.SixFunctorOperationDatum` (the fixed operation and comparison data used
  by the datum dependency).
- `WeilConjectures.CompactSupportFiniteProjection.component` and its surrounding
  projection declarations from `Sheaf.Paper.ConstructibleProjectionMates` (the recorded
  compact-support projection component).
- `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage` and its
  `projection` field from `Sheaf.Paper.ExchangeProjectionSuppliedDomains` (the supplied
  exchange/projection construction used by the projection datum).
- `WeilConjectures.canonicalCommonStagePullbackTensor` from
  `Sheaf.Paper.CompletedPullbackTensorComparison` (the canonical completed
  pullback/tensor comparison).
- `WeilConjectures.sfIntegralConstructible` and
  `WeilConjectures.sfIntegralConstructibleCategory` from
  `Sheaf.Paper.SfIntegralConstructible` (derived-complete integral constructible
  objects and their full subcategory).

Edge cases checked against the existing definition and docstring: arbitrary `N` is
quantified (so the identity and zero objects and every constant quotient are included),
`K` is not restricted to finite-Tor, the compactification is supplied explicitly, and
no separatedness assumption is added for the structure morphisms of `X` or `Y`.
The existing definition retains the specified completed integral operations and
normalized associators rather than replacing them by an arbitrary map.

Searches actually run with `msearch.py NG lem-sf-projection-reduction-integral`:

- LeanFinder query: `Tensor action associativity of a proper adjunction projection
  followed by open extension tensor comparison at completed integral adic coefficients`.
  Eight adic-completion/tensor hits, including
  `AdicCompletion.tensor_map_id_left_eq_map`; no compactification equation.
- Loogle query: `CategoryTheory.Adjunction, "projection"`. Zero hits.
- Mathlib grep query:
  `projection.*(tensorAction|[Aa]ssociat|[Rr]eduction)|compactSupportProjection`.
  Five unrelated hits on setoid projections, Dold--Kan projections, idempotents,
  and simps implementation.
- LeanSearch query: `Tensor action associativity of a proper adjunction projection
  followed by open extension tensor comparison at completed integral adic coefficients`.
  Eight hits, including `CategoryTheory.Adjunction.map_μ_comp_counit_app_tensor_assoc`,
  a generic monoidal-adjunction identity; none states this normalized geometric equation.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item id and projection
  reduction patterns found the exact existing declaration in
  `Sheaf/Paper/ProjectionFormulaCoherence.lean`. The prescribed item-id grep over
  `WeilConjectures` gave no hit. A name search in `dag/lean_names_upstream.json`
  gave no additional binding. No repair note exists for this item; the parent's
  resolved re-split note expressly names this existing theorem for the new node.

No statement correction or disputed assertion was found. No new nodes or dependency
modules are needed because the recorded declaration is the exact existing statement.

## Second reading by NG

This is the author's second pass, not an independent review. The dispatcher forbids
starting other agents; the maintainer supplies the independent review.
I reread the node, the definition `sixFunctorProjectionIntegralReductionSquare`, and
the theorem header. The theorem's binders and conclusion match the node's hypotheses
and displayed clauses, including the arbitrary third tensor factor and all coefficient
normalization data. The node copy changes only its `lean` field; the existing source
module is the recorded module and the signature in the node is verbatim up to the proof delimiter `:=`.

Clause-by-clause equation audit in the existing square definition (lines 1101--1127):

- `TX := S.higher.integralTensor X` and `TY := S.higher.integralTensor Y` are the
  datum tensors. `F := S.higher.integral.support f c` retains the supplied
  compactification, and `U := S.higher.integral.pull f` is its specified pullback.
- `compactSupportProjectionComponent S.higher.integralExchange f c` is the
  proper-counit/open-tensor composite, with no invertibility assertion or hypothesis.
- `sixFunctorProjectionTensorAssociator` conjugates
  `pullbackTensorIntegralAssociator` by `integralTensorNormalization`, giving the
  node's `a_X` and `a_Y` with exactly the indicated directions.
- `sixFunctorProjectionIntegralMu` (lines 492--512) conjugates the recorded
  `canonicalIntegralPullbackTensor` by the datum's pullback and tensor equalities.
  Its direction is `U(L tensor N) ≅ UL tensor UN`.
- `(TY.flip.obj N).map (P K L) ≫ P (K tensor UL) N` is the displayed left route.
  Lean's composition order is left-to-right.
- The right route is `(aY (F.obj K) L N).hom ≫ P K (L tensor N) ≫
  F.map (1_K tensor mu_f) ≫ F.map (aX K (U.obj L) (U.obj N)).inv`.
  The last two functor images remain separate, in exactly the printed order.
- Both routes start at `(FK tensor L) tensor N` and finish at
  `F((K tensor UL) tensor UN)`. Quantification over all `N` includes the
  degree-zero constant quotient for any ideal, including J=0 and J=R. This is
  tensor in the original integral category, never reduction of a rational object.
- `sfIntegralConstructible` is explicitly completeness plus all positive
  constructible reductions and one uniform cohomological interval. Its existing
  full-subcategory definition does not impose a separate finite-Tor predicate.

The current blueprint proof's final clause refers to prop-sf-pf-reduction (1).
The item's source preserves this exact integral source theorem and its proof plan;
that is the source used to compare this specialized node with its existing statement.

Record-format check: removed the proof delimiter `:=` from `lean.statement`; the
signature is recorded exactly up to that delimiter, matching the stage-2 reader.
