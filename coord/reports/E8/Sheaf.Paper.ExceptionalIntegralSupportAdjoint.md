## What changed

Repaired `Sheaf.Paper.ExceptionalIntegralSupportAdjoint` by importing the published
integral reconstruction and transporting its prescribed adjunction to the literal
finite-Tor compact-support lift. The proof explicitly transports the integral
constructible and common Tor-amplitude predicates across the prescribed realization
isomorphism, then uses full faithfulness of the target inclusion to transport the
adjunction. The module import was changed from the unavailable quarantined data
module to `Sheaf.SixFunctors.ExceptionalIntegralReconstruction`.

## Proved and sorry left

The declaration `exists_integral_support_adjoint` is proved. The split-off declarations
`integral_support_preservation` (node `lem-sf-integral-support-preservation`) and
`integral_support_adjoint_of_preservation` (node
`lem-sf-integral-support-adjoint-of-preservation`) remain as named `sorry`s for
parallel workers.

## No longer needed

The four former proof dependencies `lem-sf-exceptional-finite-operations`,
`lem-sf-exceptional-system-transport`, `lem-pur-normalized-reconstruction-adjunction-calculus`,
and `lem-sf-integral-compactification-system-realization` are not used directly;
they are subsumed by the existing `lem-sf-exceptional-integral-reconstruction`
theorem. The unavailable direct import of
`Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData` is replaced by
the reconstruction interface import.

## Where the brief, the DAG or earlier work was wrong

The global build record identified a bad import: the item imported a module that
had been quarantined. The original DAG proof plan duplicated the already assembled
integral reconstruction route; the delivered proof uses that assembled theorem and
its canonical prescribed realization instead.

## New nodes

`lem-sf-integral-support-preservation` records the preservation component as a
strictly smaller theorem. `lem-sf-integral-support-adjoint-of-preservation`
records the adjunction component under an explicit preservation hypothesis. Both
are imported by the repaired item and are left as named proof obligations for
parallel workers.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalIntegralSupportAdjoint": "2e1ac3a56dee7137e759447d24a5569987a192aa", "Sheaf.Paper.IntegralSupportAdjointOfPreservation": "641dc8a43454302fd70463a3772e17ce3fbda246", "Sheaf.Paper.IntegralSupportPreservation": "956b4ee962764988731c54d2d7be221b7f4ead04"}, "results": {}, "time": "2026-10-28T01:06:58+0800", "transitive": 0, "version": 1}
```

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
