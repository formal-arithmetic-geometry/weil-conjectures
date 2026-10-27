## What changed

Constructed the diagonal as the inverse of the ramified finite-level pullback comparison,
at index m = e(n+1)-1. Reused the existing coefficient quotient comparison and finite
pullback comparison, after identifying their completed coefficient maps and ordinary
scalar functors with this item's canonical ones. Proved both triangle identities by
cancelling the isomorphism and checking nested unit generators, using the existing
scalar-pullback extensionality and composite transition formulas.

All changes are inside the assigned module and its node. The theorem statement and
public imports are unchanged. No source-library declaration was changed.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.integralScalarPullbackTransitionFactorization`.
No new holes or split-off statements were added. The assigned module has zero `sorry`.

The proof uses the already stated
`WeilConjectures.RamifiedPullback.coefficients_exists` and
`WeilConjectures.RamifiedPullback.finitePullbackComparison_exists`, whose existing
proof obligations remain in their own modules. These are existing dependencies,
not new holes in this delivery.

## No longer needed

The planned direct application of
`lem-weil-pbc-completed-constant-sheaf-reduction` is replaced by the more specific
existing ramified coefficient comparison. The DVR calculation is reused through the
proved arithmetic helper of `RamifiedPullbackTowerIdentification`.
No public imports were removed, and no module or declaration was withdrawn.
No additional decomposition, cone lemma, Roos construction, derived tensor argument,
or transition-coherence theorem is needed: the generator formulas prove both triangles.

## Where the brief, the DAG or earlier work was wrong

The existing ramified coefficient and finite pullback comparison declarations already
provide the substantial finite-level identification. They apply to arbitrary schemes.
The bundled tower identification assumes invertibility of the residue characteristic,
so the proof uses its proved arithmetic helper and the underlying comparisons instead
of applying that bundled theorem. The node's proof dependencies now record this reuse.
There is no statement repair and no new hypothesis.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
