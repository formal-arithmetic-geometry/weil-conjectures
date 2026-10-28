## What changed

Restored the complete mate proof for
`WeilConjectures.IntegralFiniteExtension.finiteU_quotient_transition_mate` and
kept its hom-equivalence-injectivity consequence
`finiteU_quotient_transition`. The item now imports the coefficient-only unit
composition and realization restriction-square lemmas used by the proof,
together with the existing finite coefficient mate infrastructure.

Added the two strictly lower statement modules required by the proof:
`Sheaf.SixFunctors.FiniteCoefficientUnitComposition` and
`Sheaf.SixFunctors.CoefFiniteRealizationRestrictionSquare`. Their proofs remain
named split-off statements with documented sources and proof plans.

## Proved and sorry left

Closed one existing hole:
`WeilConjectures.IntegralFiniteExtension.finiteU_quotient_transition_mate`
(`lem-sf-finite-dualizing-mixed-quotient-mate`). The consequence
`finiteU_quotient_transition` is proved by injectivity of the scalar adjunction
hom equivalence.

Two strictly simpler split-off statements remain sorry:

- `WeilConjectures.finiteCoefficient_unit_composition`, in
  `lem-sf-finite-coefficient-unit-composition`.
- `WeilConjectures.IntegralFiniteExtension.finiteRealization_restriction_square`,
  in `lem-sf-finite-realization-restriction-square`.

No definition or private declaration contains sorry.

## No longer needed

The proof uses the finite coefficient chain and mate calculus directly, so the
old proof dependencies `lem-coef-finite-free-extension`, `lem-coef-finite-dualizing`,
and `lem-pur-compact-support-integral-coefficient-comparison` are not needed by
the item route. No public import or existing module is withdrawn; other parents
may still use those nodes.

## Where the brief, the DAG or earlier work was wrong

The earlier route left the entire mate calculation as one opaque sorry and sent
the proof through finite-free and integral compact-support machinery. The
finite-coefficient coefficient-chain theorem, exceptional counit mate cocycle,
and normalized realization square provide a shorter route. The final assembly
is a genuine mate calculation; the two remaining holes are coefficient-only
normalization lemmas strictly below the assigned statement.

The historical build-error entry mentions a missing scalar-reduction import,
but the current restored source imports `CoefScalarReductionExchange` and the
item compiles in the sandbox.

## New nodes

`lem-sf-finite-coefficient-unit-composition` records the regular scalar-unit
composition equation before exceptional or dualizing functors are introduced.

`lem-sf-finite-realization-restriction-square` records the coefficient-only
comparison-site realization restriction square for arbitrary finite coefficient
objects.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient": "185e6c5f41def5451d93ce79e8ead46b994514e8", "Sheaf.SixFunctors.CoefFiniteRealizationRestrictionSquare": "0fe8996bc9700700883d8e11163b9138de3d4882", "Sheaf.SixFunctors.FiniteCoefficientUnitComposition": "786f5db4b7a73de029d776649147b479c2d69a25"}, "results": {"Sheaf.SixFunctors.CoefIntegralFiniteDualizingCoherence": {"hash": "33e6258868e735e99734a98c2ddda6fb4b2830e1", "status": "OK"}}, "seconds": 23, "time": "2026-10-28T09:50:13+0800", "transitive": 0, "version": 1}
```

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
