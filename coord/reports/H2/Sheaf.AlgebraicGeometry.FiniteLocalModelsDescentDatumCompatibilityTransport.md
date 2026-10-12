## What changed

Added separate diagonal and cocycle theorem modules. The diagonal theorem is proved from
naturality and compatibility. The cocycle theorem is stated as the remaining universal
triple-overlap argument and is used by the original theorem, which now composes both lemmas.

## Proved and sorry left

Proved: `finiteLocalModels_descentDatum_compatibility_transport_diagonal`.
The original `finiteLocalModels_descentDatum_compatibility_transport` is proved by conjunction.
Sorry left: `finiteLocalModels_descentDatum_compatibility_transport_cocycle`.

## No longer needed

No imports or existing proof dependencies were pruned; the compatibility datum remains needed.

## Where the brief, the DAG or earlier work was wrong

The original node bundled two substantial universal arguments into one theorem. Splitting the
identity and cocycle laws gives a strictly simpler proved component and a separately reviewable
remaining statement.

## New nodes

`lem-weil-pbc-finite-local-model-compatible-transport-diagonal` and
`lem-weil-pbc-finite-local-model-compatible-transport-cocycle` record the two split statements.

## Second reading by H2

1. Compared the delivered transport module and compatibility-datum module with the repository;
   existing declaration signatures are unchanged. Verdict: pass.
2. Compiled all four delivered modules with `lcompile.py`; there are no errors, forbidden
   declarations, or sorries except the named cocycle split theorem (and the pre-existing
   compatibility-datum existence theorem). The diagonal and assembled theorem have only the
   permitted foundational axioms, while the cocycle theorem depends on `sorryAx` as reported.
   Verdict: pass.
3. Checked both split statements against their DAG nodes and searched the library for duplicates;
   the diagonal is proved and the cocycle is a strictly smaller remaining universal law, with
   source and proof documentation. Verdict: pass.
4. The diagonal proof uses the shortest available local route and the cocycle remains the only
   unresolved argument; proof-only imports are plain `import`. No unused imports or prunable
   proof dependencies were found. Verdict: pass.
5. The item node now records the conjunction route through the diagonal and cocycle nodes, and
   the unit route and `realized` fields are unchanged. Verdict: pass.

Changed only the proof modules and this review report; no statement or definition was altered.
