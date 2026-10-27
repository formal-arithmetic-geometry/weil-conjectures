## What changed

Proved `integralSupportProjectionTransport` by pasting a proper finite projection equation
and an open finite evaluation equation. The original theorem's statement and public imports
are unchanged. Added proof imports of `IntegralProperFiniteProjection` and
`IntegralOpenFiniteEvaluation` and updated the assigned node's proof dependencies.

The two new modules construct the proper and open scalar comparison maps in exactly the
published `finiteReductionIso`, `finiteDirectImage_eq` and `finiteOpenIso` coordinates.
These constructions contain no postponed data. The assembly proves the finite comparison
factorization, cancellation of the actual reconstruction unit by the adjunction triangle,
and the final scalar-adjunction projection calculation.

Validation: both new modules compiled in import order through `lcompile.py`; the final
assigned module compiled against them in 15.6 seconds with no warnings. The assigned
signature is unchanged, all Lean lines are at most 100 characters, and each node's verbatim
Lean statement and proof-dependency union were checked against the delivered files.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralSystemRealization.integralSupportProjectionTransport` from two
strictly smaller statements. This is a decomposition, not a net closure of the proof chain:
1 hole closed, 2 holes added, net -1. The assigned module has no remaining holes.

The remaining holes are:

- `WeilConjectures.IntegralSystemRealization.integralProperFiniteProjection`, node
  `lem-sf-integral-proper-finite-projection`: only the proper direct-image projection
  square, for an arbitrary system; no open extension or compactification.
- `WeilConjectures.IntegralSystemRealization.integralOpenFiniteEvaluation`, node
  `lem-sf-integral-open-finite-evaluation`: only finite evaluation of the open reduction
  mate; no proper image, total-limit projection, or inverse reconstruction unit.

Both statements retain the existing `RealizationModel` and its normalization. Their
source and complete proof plans are in their docstrings and DAG nodes.

## No longer needed

No public imports removed; no existing module or node withdrawn. The original bridge and
operations nodes remain statement dependencies, and remain needed by both primitive
calculations. The coefficient calculus, scalar adjunction, and integral compact-support
coefficient comparison remain used. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan correctly distinguishes proper projection and open evaluation,
but none of its cited Lean declarations states either normalized square. The new statements
make exactly those two individual steps explicit. The finite pasting and reconstruction-unit
cancellation are proved in the assigned module, rather than postponed as another form of
the full support projection transport. No false statement or definition repair was found.

## New nodes

`lem-sf-integral-proper-finite-projection` carries the proper scalar comparison construction
and the proper projection square, corresponding to Step 1 of the original plan.

`lem-sf-integral-open-finite-evaluation` carries the open scalar comparison construction
and finite evaluation of the open-adjunction mate, corresponding to the open part of
Step 2 of the original plan. Both follow the coefficient preservation of evaluation and
adjunction units/counits in `fix-prop-coherence.proof.md`. Searches found general adjunction
naturality lemmas but no existing normalized geometric square. Blueprint searches for
`model.push`, `openReduction` and reconstruction projections found no duplicate statement.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
