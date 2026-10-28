## What changed

Replaced the hole in `WeilConjectures.RationalVerdier.integralBeta_naturality` with
an evaluation-transpose proof. Private proved helpers establish first-variable
naturality of the ordinary Hom comparison, conjugate it through the completion
maps, and postcompose with the fixed dualizing map to obtain integral beta
naturality. The rational object and pure-tensor equations then identify both
composites with the same scalar tensor of this integral equation.

Added the proof-only import `Sheaf.Paper.IntegralHomEvaluationNaturality` and
updated the item's node to record this theorem and the existing finite-extension
models explicitly. All existing public signatures and definitions are unchanged.

Validation: the delivered module compiled cleanly through `lcompile.py` in 35.5 s.
The existing theorem header is byte-for-byte unchanged; there are no `sorry`
tokens or lines longer than 100 characters in the module. The added proof import
passes the import-direction check.

## Proved and sorry left

Closed the one hole in
`WeilConjectures.RationalVerdier.integralBeta_naturality`
(node `lem-coef-rational-verdier-integral-beta-naturality`).
No holes added, no split statements, and no `sorry` remains in the delivered module.

## No longer needed

None. Every original declared dependency is still used. No existing imports,
modules, or nodes are withdrawn. The proof does not require the integral
finite-extension invertibility, reduction-pairing, or composition theorems; it
uses the actual comparison definitions and evaluation naturality directly.

## Where the brief, the DAG or earlier work was wrong

The original proof step cited only definitions. Its evaluation-naturalness step
needs the existing `IntegralHom.evaluation_naturality`; this is now recorded as a
proof dependency. No mathematical statement was changed. Completion naturality
is proved by cancellation of the specified comparison isomorphisms, rather than
by any faithfulness assumption about finite reductions or rational localization.

The current server queue lists this as a one-hole proof item. Its older rework
row refers to the quarantined IntegralNormalizedFamily import chain, while the
restored current module has no build-error record and compiles with the current
published dependencies.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierIntegralBetaNaturality": "0c89e1fb28eaf64430ca9e4ce2fd6b82d1bd987b"}, "results": {"Sheaf.SixFunctors.RationalVerdierComparisonNaturality": {"hash": "3d79e54b9fde0b6d9af17262973d5fbf697ac193", "status": "OK"}}, "seconds": 63, "time": "2026-10-28T09:46:40+0800", "transitive": 0, "version": 1}
```

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
