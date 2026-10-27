## What changed

Restored the assigned module from quarantine and replaced its single proof hole by an assembly of two strictly simpler public obligations. `IntegralSystemProperOpenTransportCore` supplies the gamma, adjunct, and canonical clauses. `IntegralSystemProperOpenTransportPasting` supplies the vertical, horizontal, and base-change clauses for a supplied gamma. The assigned theorem assembles these fields into `ProperOpenCoherence`. The assigned module now has no `sorry`; the two split obligations retain their documented `sorry` proofs.

The stale rework import record referred to `WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeOpenImmersion`; the restored module uses the existing `Sheaf.SixFunctors.IntegralCompactificationRealizationData` import and compiles with the current published dependencies.

## Proved and sorry left

The assigned declaration `WeilConjectures.IntegralSystemRealization.integralSystemProperOpenTransport` is proved by real Lean assembly and has zero remaining `sorry`s. Two strictly simpler declarations are split off and remain sorry:

- `WeilConjectures.IntegralSystemRealization.integralSystemProperOpenTransportCore` (node `lem-sf-integral-system-proper-open-transport-core`), containing only gamma, adjunct, and canonical fields.
- `WeilConjectures.IntegralSystemRealization.integralSystemProperOpenTransportPasting` (node `lem-sf-integral-system-proper-open-transport-pasting`), containing only vertical, horizontal, and base-change fields for a supplied gamma.

## No longer needed

The original direct proof dependencies `lem-coef-semilinear-derived-sections` and `lem-sf-semilinear-proper-open-mate-pasting` are consumed by the two split obligations rather than directly by the assigned theorem. No declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier one-node proof plan compressed two independent transport tasks into one large structure construction. The current Lean proof separates the core bridge transport from the three mate-pasting equations without changing the target statement or weakening any field. The prior global build error was an obsolete bad-import record from the rework cluster; the current source import is present and compiles.

## New nodes

`lem-sf-integral-system-proper-open-transport-core` and `lem-sf-integral-system-proper-open-transport-pasting` are new split nodes with corresponding modules and complete proof descriptions in their docstrings. Their DAG records and Lean attachments are included in this delivery.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralSystemProperOpenTransport": "1643625951e7e17d8c573ab828f1cf004e10d2b3", "Sheaf.SixFunctors.IntegralSystemProperOpenTransportCore": "9330905703b81f31f0d34c656ebbd01d8012ff30", "Sheaf.SixFunctors.IntegralSystemProperOpenTransportPasting": "3d65cf6f4a94b8d46d93161990fad31c5d9365bb"}, "results": {}, "time": "2026-10-28T00:55:38+0800", "transitive": 0, "version": 1}
```

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
