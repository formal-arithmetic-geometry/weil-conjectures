## Reason

The assigned theorem is stated for continuous-function coefficient modules, while the existing
proper exchange theorem is available after restriction to constant coefficient modules. A
separate transport declaration is required to connect those presentations.

## Old

The assigned module contained one `sorry` proof and had no coefficient-transport module.

## New

This delivery adds the proof-only module
`Sheaf.Paper.FiniteCoefficientExchangeTransport` and its public transport theorem
`AlgebraicGeometry.Scheme.finiteOriginToConstant_map_ambientExchange_isIso`. The assigned
module imports that theorem and uses exact restriction-of-scalars reflection to prove
`finiteLevelProEtaleBaseChange`.

The new declaration is required because the existing constant-coefficient proper exchange
theorem applies after coefficient restriction, while the assigned statement is written in the
continuous-function coefficient presentation. The transport theorem is recorded as the
strictly smaller split node `lem-weil-pbc-finite-origin-exchange-transport`.

No existing declaration signatures were changed. The assigned module only gained proof imports
and its theorem proof; its public statement is unchanged.

## Users

`Sheaf.Paper.FiniteLevelProEtaleBaseChange` imports the new transport module. The new transport
node is used by the assigned theorem’s proof dependency graph.

## Status

landed 20261021T004830-L-1792209 2026-10-21 (merge of deliver/J4/Sheaf.Paper.FiniteLevelProEtaleBaseChange)
named split `sorry`, with its source proof plan in the declaration docstring and DAG node.
