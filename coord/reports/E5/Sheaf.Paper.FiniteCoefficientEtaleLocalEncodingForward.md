## What changed

Proved `AlgebraicGeometry.Scheme.finiteCoefficient_etaleLocal_encoding_forward` by reducing the displayed fixed-model conclusion to the existing intrinsic fixed-model comparison and the counit isomorphism of `proEtaleModuleEncoding`. Added one strictly simpler bridge theorem, `finiteCoefficient_etaleLocal_encoding_forward_bridge`, for the etale-local hypothesis to imply the intrinsic finitely presented pro-etale local-model predicate.

## Proved and sorry left

Closed the sorry in `finiteCoefficient_etaleLocal_encoding_forward`. One strictly simpler sorry remains in `finiteCoefficient_etaleLocal_encoding_forward_bridge`; it isolates the etale-to-pro-etale covering transport and normalized scalar/module comparison.

## No longer needed

No declared proof dependency was removed. The parent proof uses the finite-coefficient slice restriction, the intrinsic fixed-model comparison, and the module-encoding counit. The localization and constant-module comparison declarations remain dependencies of the bridge statement.

## Where the brief, the DAG or earlier work was wrong

The original page-sized proof plan lacked a Lean statement for the transport from the displayed ringed etale-local predicate to the intrinsic fixed-coefficient pro-etale local-model predicate. This delivery adds that strictly simpler intermediate statement.

## New nodes

`lem-weil-pbc-finite-coefficient-etale-local-encoding-forward-bridge` records the split-off transport statement.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteCoefficientEtaleLocalEncodingForward": "e4ede6262224780ca68fc5ceb49ee3b8abc9f3dc", "Sheaf.Paper.FiniteCoefficientEtaleLocalEncodingForwardBridge": "bbe2aee33a8a94c4ad7ec0e42312ec81c75ccae8"}, "results": {}, "time": "2026-10-28T00:23:25+0800", "transitive": 0, "version": 1}
```

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
