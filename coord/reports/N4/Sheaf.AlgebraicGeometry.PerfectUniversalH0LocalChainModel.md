## What changed

Completed the proof of `AlgebraicGeometry.Scheme.perfect_universalH0_local_chain_model`
with its public statement unchanged. The proof uses the existing bottom-model theorem,
exact restriction and homology comparison, the affine chain-map representative theorem,
and a private `bottom_component_isIso` lemma for short complexes with zero incoming and
outgoing maps. It constructs the source complex explicitly as the single complex on
`B.X 0`, transports the specified arrow, and proves the required degree-zero component
isomorphism and derived-category square.

The proof-only affine representative import uses the adopted source module
`WeilConjectures.AlgebraicGeometry.PerfectAffineMapRepresentative`; the current Sheaf
alias is absent from the library source. The public source `DerivedPullback` import is
retained alongside the quarantined alias so downstream signatures resolve; this interface
change is recorded in `coord/changes/N4-perfect-universal-h0-local-chain-model-imports.md`.

## Proved and sorry left

Closed the sole original sorry in
`AlgebraicGeometry.Scheme.perfect_universalH0_local_chain_model` (node
`lem-sc-perfect-universal-h0-local-chain-model`). No sorry was added; all private helpers
are proved. The module compiles cleanly with `lcompile.py`.

## No longer needed

No mathematical proof dependency is pruned. The proof uses the existing endpoint theorem
`perfect_universalH0_bottom_model` and affine representative theorem, plus the exact-functor
homology comparison. The adopted `WeilConjectures` source imports provide the required statement vocabulary.
The withdrawn `DerivedPullback` alias is retained for compatibility with the quarantined
interface; the source import is additionally public as recorded above. No DAG node or unit
step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The repository currently has no source file for this item, but an exact completed proof was
present in the project review snapshot. Adapting its imports to the current adopted source
modules makes it compile against the present library while preserving the target statement,
unit route, and dependency declarations. No statement dispute or forced adaptation is
needed.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
