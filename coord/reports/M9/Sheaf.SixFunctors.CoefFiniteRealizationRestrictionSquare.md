## What changed

Filled `WeilConjectures.IntegralFiniteExtension.finiteRealization_restriction_square`
without changing its signature. All auxiliary declarations are private and proved.
Added the proof import
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars`
for exact derived-square pasting. No existing public interface changed.

The proof first establishes the intrinsic ordinary restriction composition equation
from the prescribed scalar-unit normalization. The scalar-unit map is surjective,
so checking its generators proves the whole equation. The comparison-site
composition equation follows by conjugation under the comparison and
restriction/coextension adjunctions, using the ordinary argument from the
proved private calculation in `NormalizedOriginComparisonCoherence`. Exact derived
localization preserves both equations. Naturality pastes them, and cancellation compares the two coefficient
factorizations. Finally the unique intrinsic quotient comparison and
`scalarQuotient_restrict` transport this square to normalized DVR restrictions.
The DAG proof and dependencies now describe these steps.

Validation: the complete delivered module compiled through `lcompile.py` in
37.1 seconds with no warnings and no `sorry`. The original public signature
was compared verbatim and is unchanged.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.IntegralFiniteExtension.finiteRealization_restriction_square`.
Holes closed: 1. Holes added: 0. Remaining holes in the delivered module: 0.
No split-off statements or other module changes.

## No longer needed

The planned dependency
`lem-weil-pbc-normalized-origin-comparison-coherence`
(`Sheaf.Paper.NormalizedOriginComparisonCoherence`) is not needed by this proof.
Its public theorem concerns a single adic coefficient tower; the present mixed
square instead uses arbitrary coefficient maps. The relevant ordinary
comparison composition calculation is proved locally and localized directly.
The adopted declaration and module are preserved. No existing import was removed
and no module was withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The DAG's informal appeal to normalized-origin
coherence needed the generic restriction calculation rather than its specialized
public scalar-extension theorem. The proof supplies that calculation explicitly.
The normalized quotient comparison is identified by its recorded heterogeneous
normalization, not by assuming it is definitionally the generic comparison.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefFiniteRealizationRestrictionSquare": "a85cf96bef314c0c9e6e0aca11a0841220e72590"}, "results": {"Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient": {"hash": "185e6c5f41def5451d93ce79e8ead46b994514e8", "status": "OK"}}, "seconds": 71, "time": "2026-10-28T10:49:38+0800", "transitive": 0, "version": 1}
```

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
