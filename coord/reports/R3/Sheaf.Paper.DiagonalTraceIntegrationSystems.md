## What changed

The item theorem now has a complete proof that obtains a normalized supported source and
then obtains the degree-zero tower witness for that source, combining the two results into
the required existential. The proof-only imports are
`Sheaf.Paper.DiagonalTraceSupportedSourceExistence` and
`Sheaf.Paper.DiagonalTraceLimitWitnessExistence`.

Two new modules state the strictly smaller obligations left by the geometric argument:
`Sheaf.Paper.DiagonalTraceSupportedSourceExistence` and
`Sheaf.Paper.DiagonalTraceLimitWitnessExistence`. Their declarations are named
`diagonalTrace_supportedSource_exists` and `diagonalTrace_limitWitness_exists`.

## Proved and sorry left

The item declaration `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_integrationSystems`
is proved. Two split obligations remain as named theorem sorries:

- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_supportedSource_exists`, node
  `lem-sfb-diagonal-trace-supported-source-existence`;
- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_limitWitness_exists`, node
  `lem-sfb-diagonal-trace-limit-witness-existence`.

No definitions contain `sorry`.

## No longer needed

The item no longer directly follows the eight original proof-dependency nodes. Those
geometric and categorical nodes remain recorded as proof dependencies of the two split
obligations, where their arguments are needed. No statement or unit-level route was
removed, and no existing public import was removed.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan describes the geometric construction but provides no Lean
interface theorem that constructs either the `SupportedSource` or the
`SingleTowerLimitWitness`. The item can therefore be assembled only after those two
strictly smaller existence statements are made explicit. The target statement and all
existing definitions are unchanged.

## New nodes

`lem-sfb-diagonal-trace-supported-source-existence` records the construction of the
normalized source for either projection and is stated as `Nonempty (SupportedSource ...)`.
`lem-sfb-diagonal-trace-limit-witness-existence` records the strict-system evaluation and
limit-comparison construction of the tower witness for a given supported source. Both
nodes are in `sec-six-functors-basics`, unit `sk-prop-diagonal-tower`, and their Lean
modules and declarations are included in this delivery.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
