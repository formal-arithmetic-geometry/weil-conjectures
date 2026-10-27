## What changed

Filled `WeilConjectures.rationalProjectionTensorCompatibility_proper` by an explicit
coefficient-change calculation for the prescribed right-adjoint projection mate.
Private proved helpers normalize the supplied stage coordinates, identify the pull
comparison with its canonical equality comparison, and prove the tensor-pullback
square from the integral/rational canonical comparison formulas. The final mate
calculation uses the actual coefficient adjunction's counit equation and naturality.
No existing declaration signature, public import, definition or instance was changed.
Local irreducibility attributes keep large background constructions from unfolding
during elaboration; they do not change the interface seen by importers. The proper
projection assembly is proved first for abstract stage categories and then specialized.

Validation: the final module compiled without warnings through `lcompile.py` in
48.6 seconds, below the 60-second limit. Profiling options were removed.

## Proved and sorry left

Closed one of the item's two original holes:
`WeilConjectures.rationalProjectionTensorCompatibility_proper`
(`lem-sf-rational-projection-tensor-compatibility-proper`).

One original hole remains unchanged:
`WeilConjectures.rationalProjectionTensorCompatibility_compactSupport`
(`lem-sf-rational-projection-tensor-compatibility-compact`). Its remaining work is
the open-adjunction unit calculation, pullback-compositor compatibility, and pasting
with the proper calculation through the support-factorization comparisons.

Added zero holes and zero split statements. All private helpers are proved.
The existing tensor functor equality and final conjunction assembly remain proved.

## No longer needed

No imports or modules were removed. The proper calculation uses the existing
operation-stage, completed tensor-pullback comparison, derived tensor/pullback, and
canonical projection declarations. It does not use the independently supplied
per-square `rationalExchangeComparison.tensor` family; the shared tensor comparison
is exactly `rationalProjectionTensorComparison` throughout. All declared dependencies
of the proper node remain needed. No unit route was bypassed.

## Where the brief, the DAG or earlier work was wrong

The prior report correctly observed that the supplied per-square tensor isomorphism
is not identified with the canonical shared tensor comparison. That prevents a direct
application of the per-square projection field, but it does not prevent the proper
mate proof: the normalized tensor-pullback formulas and coefficient counit equation
supply the required square. This delivery performs that calculation without adding
another intermediate obligation or assuming any projection-coherence law.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
