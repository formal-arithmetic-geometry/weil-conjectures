## What changed

The assigned theorem now performs a real case reduction. For a finite-Tor input it
obtains source derived completeness from the intrinsic-to-legacy comparison; for the
coefficient tensor unit it uses a dedicated source-completeness statement. Both
cases are passed to ordinary-pullback preservation of derived completeness.

Two strictly smaller intermediate statements were added in
`FiniteTorOrdinaryPullCompleteOfComplete.lean` and
`FiniteTorOrdinaryPullCompleteTensorUnit.lean`. Their proofs remain named split
obligations with source descriptions and matching DAG nodes.

## Proved and sorry left

The original `finiteTorOrdinaryPullComplete` hole is closed by a complete Lean
reduction. The following two strictly smaller obligations remain as `sorry`:

- `WeilConjectures.GeneratorReduction.finiteTorOrdinaryPullComplete_of_complete`
  (`lem-sf-finite-tor-ordinary-pull-complete-of-complete`), preserving derived
  completeness under ordinary ringed pullback.
- `WeilConjectures.GeneratorReduction.tensorUnit_complete_for_finiteTorOrdinaryPull`
  (`lem-sf-finite-tor-ordinary-pull-complete-tensor-unit`), completeness of the
  integral tensor unit.

No `sorry` occurs inside a definition.

## No longer needed

The original chart-refinement, qcqs-locality, and completed-free-resolution proof
imports are no longer used by the assigned theorem's Lean proof and are removed
from its proof dependency route. The canonical bridge and finite-Tor/derived-
completeness definitions remain used.

## Where the brief, the DAG or earlier work was wrong

The earlier proof plan treats the full local finite-projective devissage as if it
were already available as a public theorem. The library exposes the operation
objects and completeness predicates, but no public theorem carrying that devissage;
the reduction therefore isolates source-completeness preservation and tensor-unit
completeness as separate, strictly smaller statements.

## New nodes

`lem-sf-finite-tor-ordinary-pull-complete-of-complete` records the ordinary
pullback-preserves-completeness step.

`lem-sf-finite-tor-ordinary-pull-complete-tensor-unit` records the rank-one
completed-coefficient tensor-unit completeness step.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
