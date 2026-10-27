## What changed

Proved `WeilConjectures.FrobeniusExchange.directImage_linear` in
`Sheaf.Paper.SystemOperationExchangeRealization`. Reduction is additive and linear by its
recorded adjunction. The proved scalar-action helpers from
`Sheaf.Paper.CompactSupportReductionTower` establish linearity of sectionwise system direct
image, scalar restriction, inverse limit, and their derived functors. The proved
`normalizedDerivedLinear` helper from `Sheaf.Paper.CompactSupportRepresentativeIndependence`
identifies these actions with the recorded integral coefficient action. The full constructible
inclusion reflects the resulting addition and scalar identities.

Added private `import all` imports of those two modules to reuse their proved private helpers.
Updated the item's node proof, proof dependencies, and proof origin. No statement, definition,
public import, or unit route changed.

Validation: `lcompile.py` compiled the delivered item successfully in 41.0 seconds, with no
warning in the item. The compiler used its supported private overlay for unpublished
dependencies. Static checks found nine remaining `sorry` tokens and no line over 100 characters.

## Proved and sorry left

Closed one of the ten existing holes:
`WeilConjectures.FrobeniusExchange.directImage_linear`.
Added zero holes and zero split-off statements.

Nine existing holes remain, all owned by
`def-weil-system-operation-exchange-realization`:

- `WeilConjectures.FrobeniusExchange.systemDirectEvaluation_isIso`
- `WeilConjectures.FrobeniusExchange.systemExchange_evaluation`
- `WeilConjectures.FrobeniusExchange.systemOpenEvaluationInv_isIso`
- `WeilConjectures.FrobeniusExchange.systemOpenExchangeInv_isIso`
- `WeilConjectures.FrobeniusExchange.systemOpenScalarInv_isIso`
- `WeilConjectures.FrobeniusExchange.directImage_roos`
- `WeilConjectures.FrobeniusExchange.directAlpha_isIso`
- `WeilConjectures.FrobeniusExchange.compactRealization_existsUnique`
- `WeilConjectures.FrobeniusExchange.compactAlpha_isIso`

## No longer needed

None. No existing import, module, or node is pruned. The original dependencies remain needed by
retained declarations and the remaining geometric obligations. The two added proof dependencies
supply the scalar-action and derived-linearity helpers actually used by the new proof.

## Where the brief, the DAG or earlier work was wrong

No statement or definition error was found. The direct-image linearity obligation can reuse the
existing normalized scalar-action proofs, so it needs no additional geometric decomposition.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
