# WeilConjectures.TensorAdjunctionExchange: restore reviewed definition ownership

## Reason

The assigned rework row preserves the parent in
`quarantine/Sheaf/Paper/TensorAdjunctionExchange.lean`. Its global build failed at
RingModel.evaluationX, RingShifts.firstComponentsX, ChangeShifts.firstComponentsX,
OperationRealization.extraordinary and the rational projection application, with
200000-heartbeat definitional equality timeouts and cascading unknown identifiers.

The reviewed node `def-sf-tensor-hom-transposition-data` already assigns ten of the
archive's definitions to `Sheaf.SixFunctors.TensorHomTranspositionData`. Its review
requires a restored parent to import that owner and drop its duplicates. That module
is absent from both lean and quarantine in the current shared tree. This packet
reconstructs the reviewed owner from those exact archive blocks; it does not create
a new split or change the definition node's mathematical statement.

Explicit coefficient universe arguments avoid inferring large category expressions.
Normal transparency avoids unnecessary unfolding of derived-category constructions
while checking record field compositions. No heartbeat or timeout limit is raised.

## Old

The archived parent directly contains Model, Model.left, Model.right,
Model.inverseComponent, Conclusion, PartialRealization, RingModel, Projection,
RingShifts and Admissible, despite their reviewed ownership in the shared data module.
The complete original definitions remain at the quarantine path above.

The relevant original expressions are:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
structure Model {X Y : Scheme.{u}} (s : Stage.{u} l) (F : Operation l Ω X Y s) where
```

Applications use `C l Ω`, `Operation l Ω`, `System l Ω` and `s.inclusion l Ω`.
The original parent imports `Sheaf.Paper.VerdierExchange` publicly.

## New

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
structure Model {X Y : Scheme.{u}} (s : Stage.{u} l) (F : Operation.{u} l Ω X Y s) where
```

Applications instead specify the existing universe: `C.{u} l Ω`,
`Operation.{u} l Ω`, `System.{u} l Ω` and `s.inclusion.{u} l Ω`.
The parent publicly imports `Sheaf.SixFunctors.TensorHomTranspositionData`;
that owner publicly imports `Sheaf.SixFunctors.VerdierExchangeData`. All other
original imports remain. The 28 original explicitly named declarations occur
exactly once across the two restored modules, with the same namespaces, data,
field equations and theorem statement. The shared owner has zero holes.
The parent retains the original tensor_adjunction theorem hole; no new hole is added.

## Users

The source-only downstream checks with --allow-missing report zero live users for
both missing modules. A scan of quarantine and the DAG also checks the consumers
whose proofs have not yet imported the shared definitions. No consumer changes its
meaning, and no additional consumer source needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.TensorAdjunctionExchange | J8 | Restore parent and import reviewed definition owner. |
| Sheaf.SixFunctors.TensorHomTranspositionData | unclaimed | Restore ten reviewed definitions with identical public names and data. |
| Sheaf.SixFunctors.TensorHomSignedTransposes | absent; not edited | DAG consumer of unchanged Model, RingModel, Projection, Conclusion, RingShifts and Admissible. |

## Status

landed 20261025T043256-L-1693498 2026-10-25 (merge of deliver/J8/Sheaf.Paper.TensorAdjunctionExchange)
