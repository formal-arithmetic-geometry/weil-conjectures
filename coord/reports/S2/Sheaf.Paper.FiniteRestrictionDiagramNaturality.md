## What changed

The six previously landed proofs remain intact. I moved the existing geometric and
strict diagram constructions into `Sheaf.Paper.FiniteRestrictionDiagramModels`, with
identical declarations and bodies, so the remaining theorem can import two independent
argument steps. I added `Sheaf.Paper.FiniteRestrictionStrictTransport` for strict
isomorphisms and exchange/restriction commutativity, and
`Sheaf.Paper.FiniteRestrictionConstructibleVertices` for constructibility of completed
square vertices. The main theorem now combines these statements, finite point
finiteness, completion reindexing laws, and functorial preservation of commutative
squares. The required model move is recorded in
`coord/changes/S2-finite-restriction-diagram-models.md`.

All four sandbox modules compile with the server compiler.

## Proved and sorry left

The following original holes are closed and unchanged from the prior landing:
`geometry`, `points_existsUnique`, `point_paths`, `sum_existsUnique`, `inputNaturality`,
and `finiteRestrictionDiagramNaturality_commonStage`.

`finiteRestrictionDiagramNaturality` is now proved by a complete Lean proof from two
strictly simpler named statements. Two new holes are split off:

- `finiteRestrictionStrictTransport`, node `lem-zl-finite-restriction-strict-transport`;
- `finiteRestrictionConstructibleVertices`, node `lem-zl-finite-restriction-constructible-vertices`.

The construction declarations moved to `FiniteRestrictionDiagramModels` are definitions
with no holes. No other `sorry` was added.

## No longer needed

No mathematical dependency node is withdrawn. The model move replaces the former
same-file construction dependency with `def-zl-finite-restriction-diagram-models`.
The proof uses the strict counit/restriction towers, finite integral fibre reconstruction,
completion reindexing, rationalization, finite coefficient point functor, algebraically
closed coefficient inclusion, and finite-field residue invertibility. The old proof-only
imports of isomorphism field transport, completed operation substitution, pullback scalar
identities, and sectionwise inverse-image transport are no longer needed by the six
previous proofs and remain absent from the theorem module.

## Where the brief, the DAG or earlier work was wrong

The earlier proof packet left the top theorem as a `sorry` while proving its six helper
and downstream theorems. The remaining theorem is reducible to strict transport and
constructibility statements, so those two statements are recorded as new DAG nodes.
No target statement or existing construction signature was changed.

## New nodes

`def-zl-finite-restriction-diagram-models` owns the relocated construction declarations.
`lem-zl-finite-restriction-strict-transport` states strict isomorphism and square
commutativity before completion. `lem-zl-finite-restriction-constructible-vertices`
states only the completed object constructibility needed for the rationalized square.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
