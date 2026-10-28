## Worker report

The item is already stated exactly by
`WeilConjectures.sixFunctorProjection_reduction_common` in
`Sheaf.Paper.ProjectionFormulaCoherence`, lines 1246–1253 of the read clone.
Record it with `existing: true`; no Lean module is added. Its proof is still `sorry`.
Only the node's `lean` field changes. No statement correction, new definition node,
or dependency repair is needed.

Read the current blueprint proof at
`literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md`,
the item's full source quotation and seven-step proof, and the source theorem's
docstring and signature. The existing docstring explains proper counit transposition,
the open unit calculation, pasting, coherent completion, localization, and passage
to a common finite coefficient field. This is a statement binding, not a claim
that this postponed proof has been completed.

Hypothesis and clause correspondence:

- The finite field, characteristic, algebraic closure, and finite-type base are
  packaged in `D : FiniteFieldDatum.{u}`. `C : D.CoefficientDatum` supplies the prime
  `C.l`, `C.different : C.l ≠ D.p`, and `C.Qbar` with its field, algebra, and
  algebraic-closure instances. These are the theorem's explicitly declared section
  parameters, not auto-bound variables.
- The finite extension is `E : Type u` with `[Field E]`, `[Algebra (Padic C.l) E]`,
  and `[FiniteDimensional (Padic C.l) E]`; `n : ℕ` and `hn : 1 ≤ n` give the
  positive finite coefficient level. The valuation-ring and quotient constructions
  are the existing coefficient constructions inside the operation datum. An
  embedding of E into the closure is auxiliary to choosing representatives; the
  common category and its operation datum already contain all finite stages.
- `S : SixFunctorDatum D C E n hn` is exactly the specified six-functor datum,
  extending `SixFunctorOperationDatum` and retaining the actual operation and
  normalization data.
- `{X Y : SixFunctorSpace D}` are finite-type k-schemes. This is the full
  subcategory of `Over (Spec (.of D.k))` cut out by `LocallyOfFiniteType` and
  `QuasiCompact` of the structure map; it does not require separated structure
  maps. `(f : X ⟶ Y) [IsSeparated f.hom.left]` is the separated k-morphism.
  Its finite-type property follows in this finite-type-over-a-field setting.
- `(c : Compactification f.hom.left)` supplies the actual open/proper
  factorization and its equality with f; the compactification is not replaced
  by an existence hypothesis or a newly chosen representative.
- K has type `generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left`;
  L and N have the same category over Y. These are the literal common finite-stage
  pair categories. No finite-Tor, perfectness, flatness, or projection-invertibility
  hypothesis occurs.
- The conclusion is `sixFunctorProjectionCommonReductionSquare S f c K L N`.
  Opening this definition (lines 1205–1233), `TX` and `TY` are
  `S.closure.commonStageTensor X` and `... Y`; F is
  `S.closure.commonStage.support f c`, and U is `S.closure.commonStage.pull f`.
- P is `compactSupportProjectionComponent S.closure.commonStageExchange f c`.
  Its definition evaluates the recorded projection on the identity base-change
  square retaining c. `ExchangeProjectionStage.projection` transports the proper
  counit projection followed by the open comparison using the recorded support
  identification. It is the actual component, not an arbitrary isomorphism.
- The left route is `(TY.flip.obj N).map (P K L) ≫ P ((TX.obj K).obj (U.obj L)) N`,
  rendering `(P(K,L) ⊗ 1_N)` followed by `P(K ⊗ UL,N)`.
- `aX` and `aY` are `sixFunctorProjectionTensorAssociator` applied to the datum's
  tensor normalizations and `pullbackTensorCommonAssociator`. This is precisely
  conjugation of the canonical associator by the recorded tensor equality.
- The right route is `(aY (F.obj K) L N).hom ≫ P K ((TY.obj L).obj N) ≫
  F.map ((TX.obj K).map (sixFunctorProjectionCommonMu S f L N).hom) ≫
  F.map (aX K (U.obj L) (U.obj N)).inv`. Lean's composition is in forward order.
  In particular the final two `F.map` expressions are separate, with the tensor
  pullback map first and the inverse associator last.
- `sixFunctorProjectionCommonMu` conjugates
  `canonicalCommonStagePullbackTensor C.l C.Qbar f.hom.left` by the datum's
  pullback and tensor equalities. Its source is U(L tensor N) and its target
  UL tensor UN, exactly the required orientation.
- Both routes run from `(FK tensor L) tensor N` to
  `F ((K tensor UL) tensor UN)`, as the definition's typed composition shows.
- The constant quotient clause is substitution into the arbitrary N binder.
  U is applied to that same N. No functor from rational coefficients to finite
  coefficients is introduced; there is no additional independent equality needed.

Dependency declarations inspected and used by this existing interface:

- `Sheaf.Paper.SixFunctorDatum`: `WeilConjectures.SixFunctorDatum`.
- `Sheaf.Paper.SixFunctorOperationDatum`:
  `WeilConjectures.SixFunctorOperationDatum`, including its `closure` field.
- `Sheaf.Paper.ConstructibleProjectionMates`:
  `WeilConjectures.compactSupportProjectionSquare` and
  `WeilConjectures.compactSupportProjectionComponent` (the general-stage helper
  explicitly recorded in that dependency's `lean.declarations`). Its primary
  finite-stage `CompactSupportFiniteProjection.component` is not substituted
  for the common-stage component.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage` and its
  `projection`, built from `compactificationProjectionFromData`.
- `Sheaf.Paper.CompletedPullbackTensorComparison`:
  `WeilConjectures.canonicalCommonStagePullbackTensor` and its uniquely normalized
  common-stage representative characterization.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`.

Read each dependency node's full statement, record, and the corresponding source
signatures and docstrings. The generic component and supplied-domain projection
retain the dependency declarations; nothing requires a replacement interface.

Edge cases checked by reading the quantified domains and arrow directions:
identity f and identity compactifications are included; empty X or Y is not
excluded by SixFunctorSpace; zero K, L, or N has no extra restriction. All N,
including the tensor unit and constant quotients, are allowed. For the field
Lambda = C.Qbar, J = 0 gives the unchanged coefficient object and J = top gives
zero; these exhaust the ideal quotients of a field. Arbitrary nonconstant N is
still covered. Different representatives and larger common finite fields are
retained through the canonical common-stage comparison. No new claim is proved.

Searches (2026-10-28; all msearch commands used group NC and this item):

- `leanfinder`: "The compact support projection formula for algebraically closed
  l-adic common finite-stage coefficients is compatible with right tensor action
  by an arbitrary constructible object and the tensor associator". Eight hits,
  all general LightCondensed tensor/internal-projectivity declarations; no match.
- `loogle`: `CategoryTheory.Adjunction, "projection"`. Zero hits.
- `leansearch`: "The compact support projection formula at common algebraically
  closed l-adic coefficients satisfies tensor action associativity for arbitrary
  constructible inputs". Eight general tensor/coalgebra associativity hits; no
  statement about these specified common-stage maps.
- Mathlib `grep` through msearch:
  `projection.*(tensorAction|[Aa]ssociat|[Rr]eduction)|compactSupportProjection`.
  Five unrelated idempotent, partition, tactic, and Dold–Kan projection hits.
- The same pattern with `rg -n` in `lean/WeilConjectures` found generic projection
  action and etale derived projection statements. Reading
  `AlgebraicGeometry.Etale.projectionMapOfCompactification_reductionModIdeal`
  confirms that it uses ordinary etale derived categories and a constant quotient,
  rather than the present common-stage datum and arbitrary N.
- `grep -rn "lem-sf-projection-reduction-common" lean/WeilConjectures`: no hits.
- `rg -n` in `lean/Sheaf` for `sixFunctorProjection_reduction_common` and
  `sixFunctorProjectionCommonReductionSquare` found the exact declaration above.
  Searches for `sixFunctorProjectionCommonMu` and
  `sixFunctorProjectionTensorAssociator` located the canonical normalized maps
  used to check every factor of its defining equality.

Validation: this is an existing-declaration delivery, so there is no delivered
Lean file to compile (brief-stage2 section 1 and section 5). The prescribed
`deliver2.py --no-push` wrapper generates a module-mode `#check` probe, compiles
it through scompile, and runs the delivery preflight to validate the existing
binding on the server.
No node fault or statement dispute was found.

## Second reading by NC

I reread the node alongside the existing theorem, reduction-square definition,
common mu, tensor associator, and actual projection-component definitions.
This is the worker's second pass; the maintainer supplies the independent review,
as required by the dispatcher brief. No second agent was started.

The coefficient and geometry binders match the node through D, C, E, n, hn,
SixFunctorSpace, separated f, and c. The three object binders are unrestricted
common-stage objects. The reduction-square definition has exactly two arrows on
the left and four arrows on the right. Its last two factors are distinct F.map
applications, with mu.hom and aX.inv in the required order. The generic recorded
projection-component helper evaluates the datum's actual projection; the
associators and pullback tensor comparison are conjugated canonical maps.
The all-ideal sentence is specialization of arbitrary N inside the same category,
including both field ideals. No mismatch was found and no Lean source changed.
The node record stores the existing theorem's signature verbatim, ending before
`:=`, with `existing: true` and no file field.
