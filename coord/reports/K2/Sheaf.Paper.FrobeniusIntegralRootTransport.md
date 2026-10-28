## What changed

The target proof now applies two strictly simpler auxiliary statements. The additive
transport statement supplies the additive isomorphism, the root tensor formula, and
completed coefficient semilinearity. The module glue statement supplies the module
isomorphism obtained from that semilinear map and identifies it after the adjunction
unit. The target then evaluates this identity on a scalar times a pure root tensor.

Two new modules were added:

- `Sheaf.Paper.FrobeniusIntegralRootTransportAux`
- `Sheaf.Paper.FrobeniusIntegralRootTransportModuleGlue`

The corresponding DAG node copies record the changed proof route and both auxiliary
statements.

## Proved and sorry left

Closed:

- `WeilConjectures.frobeniusIntegralRootTransport` (1 sorry closed).

Added as genuine lower statements:

- `WeilConjectures.frobeniusIntegralRootTransport_additive` (1 sorry).
- `WeilConjectures.frobeniusIntegralRootTransport_moduleGlue` (1 sorry).

The additive statement omits the module adjunction and is strictly the additive part
of the target. The module glue statement has an arbitrary additive semilinear map and
omits the root comparison and tensor formula, so it is a reusable categorical step
strictly simpler than the target.

## No longer needed

No existing imports were removed from the target. The planned routes through
`Sheaf.Paper.PurIntegralTensorTransport`, `Sheaf.Paper.FirstRootLinePullback`, and the
invertibility-dependent positive-root transport are not used: the target has no
invertibility hypothesis for `l`. No additional source modules or DAG nodes from
those routes are needed by this proof.

## Where the brief, the DAG or earlier work was wrong

The direct categorical construction described by the original proof plan cannot be
elaborated in this import boundary: the sectionwise module instance for the canonical
ring direct image is supplied only by a later module whose import would cycle back to
this target. The categorical part is therefore isolated as the generic
`moduleGlue` statement, while the target itself remains a short real combination of
that statement with the additive/root formulas. This does not change the target
statement or add an invertibility assumption.

## New nodes

- `new-weil-frobenius-integral-root-transport-additive`: additive inverse-image
  transport with its root-tensor formula and completed scalar semilinearity.
- `new-weil-frobenius-integral-root-transport-module-glue`: canonical module
  adjunction transport of an arbitrary additive semilinear isomorphism.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FrobeniusIntegralRootTransport": "5485d25f6d1c738e2a6eb7ed6823b7c2a1e0d897", "Sheaf.Paper.FrobeniusIntegralRootTransportAux": "b09504ba51cbf4fb863453344db2e36eafed5a86", "Sheaf.Paper.FrobeniusIntegralRootTransportModuleGlue": "92a181409c8815c84e13c34803c4a80a84a0fcac"}, "results": {"Sheaf.Paper.FrobeniusCoefficientTwistsCanonical": {"hash": "2376159211b8ee9feb9775907954d31a6d5924ed", "status": "OK"}}, "seconds": 59, "time": "2026-10-28T07:41:14+0800", "transitive": 0, "version": 1}
```

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
