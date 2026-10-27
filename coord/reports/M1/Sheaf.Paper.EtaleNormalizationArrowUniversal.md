## What changed

Proved `AlgebraicGeometry.Scheme.etaleNormalizationArrow_universal_of_constant` in
`Sheaf.Paper.EtaleNormalizationArrowUniversal`, preserving its statement and all existing
public imports. Added private proved helpers for the natural constant/slice comparison,
its compatibility with coefficient restriction, the corresponding derived square, and
universality on the slice. The final proof transports initial structured arrows through
the existing derived étale slice equivalences and uses the existing canonical-arrow
comparison. Updated the item's proof plan and dependencies to match this argument.

The proof imports the existing constant-universality theorem, constant sheaves on slices,
the source/slice comparison (including its private proved helpers), and composition of
exact derived squares. No other existing module is changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.etaleNormalizationArrow_universal_of_constant`
(node `lem-weil-pbc-etale-constant-arrow-universal-transport`).
All private helpers are proved. Holes added: zero. Holes left in this delivery: zero.
No split-off statements or modules were added. The complete item compiled through
`lcompile.py` with no warnings in 21.1 seconds.

## No longer needed

No original imports, nodes or modules are withdrawn. The original three definition
dependencies remain needed. No scalar-extension adjunction on the étale source is
required: constant universality on the slice and equivalence transport suffice.
In particular, `Sheaf.Paper.DerivedScalarRestrictionPullbackMate` is not imported; it
already depends on this item and would create an import cycle. No pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The original plan left the compatibility of constant realization, slice restriction and
coefficient restriction implicit. This delivery proves that compatibility directly from
sheafification units and derives it using the existing exact-square composition theorem.
The generic slice helper explicitly fixes the structured-arrow functor to scalar
restriction: allowing inference from the composite codomain instead chooses slice
restriction followed by scalar restriction, which expresses a different universality
claim. The original public theorem and the unit route are unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.EtaleNormalizationArrowUniversal": "a2e7a5e0d55b09808c51984a4ef70cbbe8ef2b7d"}, "results": {"Sheaf.Paper.FinitePerfectAdicConstantUniversal": {"hash": "919f654cf2f2ecd095e2d6694aa0f8ba1911dd1d", "status": "OK"}}, "seconds": 27, "time": "2026-10-28T06:30:51+0800", "transitive": 0, "version": 1}
```

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
