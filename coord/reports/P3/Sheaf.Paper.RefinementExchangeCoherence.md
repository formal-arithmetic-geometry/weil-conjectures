## What changed

Proved `AlgebraicGeometry.ProEtale.StrictTower.refinementComparison_isIso` and
`AlgebraicGeometry.ProEtale.StrictTower.refinementFiniteOrigin_pullback` in
`lean/Sheaf/Paper/RefinementExchangeCoherence.lean`.

The first specializes `gamma_isIso` to the identity-left refinement square.
Private categorical helpers transport component invertibility along an equality
of natural transformations before specializing the strict-tower functors. This
avoids the kernel timeouts caused by directly unfolding their composite components.
The published `refinementComparison` definition is unchanged.

The second transports each existing origin separately: retain its finite ring and
scalar map, pull its bounded-below etale complex back, use the derived inverse of
`hPullbackInv`, and finish with `originIso` and `evalG`. No common coefficient ring
or bound is introduced. Choosing the witness of the supplied hypothesis occurs
only inside this theorem proof; no new data definition uses an unproved existence.

All existing signatures, definitions, visibility and imports are unchanged.
The two proofs compiled together cleanly in 4.0 seconds with the required remote
compiler. No heartbeat or time limit is increased in the delivered module.

## Proved and sorry left

Holes closed: 2 of the original 3; holes added: 0; split off: 0.

Proved:

- `AlgebraicGeometry.ProEtale.StrictTower.refinementComparison_isIso`.
- `AlgebraicGeometry.ProEtale.StrictTower.refinementFiniteOrigin_pullback`.

The one remaining sorry is the original unchanged
`AlgebraicGeometry.ProEtale.StrictTower.refinementExchangeCoherence`, belonging to
`lem-cbc-complete-proetale-refinement-exchange-coherence`.
It retains its complete source and six-step proof in its docstring. The unverified
private coherence drafts from the earlier attempt are excluded from the delivery.

## No longer needed

None. No imports, nodes or modules are pruned. The verified proofs use the
existing finite coefficient transport, strict-tower operations, proper/open
calculus, comparison pullback and etale inverse-image exactness interfaces.

## Where the brief, the DAG or earlier work was wrong

The earlier report incorrectly treated compiler unavailability as the outstanding
obstacle. The compiler now responds, and the direct component-invertibility draft
hit a kernel deterministic timeout. Equality transport at the natural-transformation
level fixes that problem without changing a definition or raising the limit.
The earlier pullback-origin draft is now verified. The final coherence theorem
is still unproved; no claim is made that the module is fully proved.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
