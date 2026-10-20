## What changed

Added two named component theorems to
`lean/Sheaf/AlgebraicGeometry/ProEtaleProjectiveLineTrace.lean`:
`exists_spP1BaseTraceConditions` for clauses (1)--(2), and
`spP1DiagonalIntegrals_of_twisted` for clause (3). The target theorem now combines
these components with an explicit existential constructor proof. The change record `coord/changes/pro-etale-projective-line-trace-components.md` records the public-interface addition. The item node records
this reduced proof route, and two new DAG nodes describe the split obligations.

## Proved and sorry left

The original target `proEtale_projectiveLine_trace` is proved from the two component
theorems. Two strictly smaller named obligations remain as `sorry`:

- `exists_spP1BaseTraceConditions`, node `lem-sp-p1-base-trace-families`;
- `spP1DiagonalIntegrals_of_twisted`, node `lem-sp-p1-diagonal-integrals-family`.

## No longer needed

The component obligations use the existing projective-line decomposition and diagonal-integral
modules; no imported module was removed. No module was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original node presented the three clauses as one monolithic theorem. The Lean
interface separates clauses (1)--(2) from clause (3), so the proof is recorded as two
strictly smaller named results and a real constructor combination.

## New nodes

`lem-sp-p1-base-trace-families` records the existence of the normalized arbitrary-base
families. `lem-sp-p1-diagonal-integrals-family` records the diagonal integral result for
any normalized twisted family.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
