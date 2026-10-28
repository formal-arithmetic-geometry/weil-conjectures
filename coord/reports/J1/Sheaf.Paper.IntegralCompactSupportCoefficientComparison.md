## What changed

Proved `WeilConjectures.PurCompactSupport.comparison_commShift` in the item module.
The proof installs the canonical shift structures for derived scalar restriction and
extension, obtains shift compatibility of the compact-support restriction square from
`restriction_commShift`, and transports it through the scalar mate using
`inverse_mate_shift`. No imports or declarations were added or removed.

## Proved and sorry left

Closed one existing sorry: `comparison_commShift`.

The following existing named theorem obligations remain unchanged: `comparison_composition`,
`comparison_identity`, `integralCoefficientComparison`, `recordedIdentification_existsUnique`,
`reductionComparison_isIso`, `refinementProperOpen_existsUnique`, `comparison_refinement`,
`refinementComparison_coherence`, `comparison_strict_towers`, and `comparison_projection`.

## No longer needed

None. The proof uses the existing `IntegralCompactSupportRestrictionShift` dependency and
its `restriction_commShift` declaration, together with the local mate-shift helper.

## Where the brief, the DAG or earlier work was wrong

Nothing identified. The DAG already listed `lem-pur-compact-support-restriction-shift`
as a proof dependency.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralCompactSupportCoefficientComparison": "0a51c86fef472f9ab8d19449a9810125d6bae7a5"}, "results": {}, "time": "2026-10-28T08:03:40+0800", "transitive": 0, "version": 1}
```

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
