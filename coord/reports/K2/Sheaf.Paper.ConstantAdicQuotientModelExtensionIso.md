## What changed

Proved `AlgebraicGeometry.Scheme.constantAdicQuotient_model_extension_iso` from two strictly smaller named steps. Added a realization-level transport theorem and a nonempty-chart conservativity theorem, each recorded as a separate stage-3 node and imported privately by the item module.

## Proved and sorry left

The assigned theorem is proved. The two split-off public theorems remain `sorry`: `constantAdicQuotient_model_realization_extension_iso` and `constantAdicQuotientRealization_reflects_iso`.

## No longer needed

None. The original scalar-comparison and derived-normalization imports remain needed by the split-off statements.

## Where the brief, the DAG or earlier work was wrong

The original proof plan grouped geometric transport and stalk conservativity into one large theorem without Lean declarations for either intermediate conclusion. The route was decomposed into those two strictly smaller conclusions; the target statement and its hypotheses are unchanged.

## New nodes

- `lem-weil-pbc-constant-adic-quotient-model-realization-extension-iso`
- `lem-weil-pbc-constant-adic-quotient-realization-reflects-iso`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ConstantAdicQuotientModelExtensionIso": "9698fc5ea81194d9f0ee084bcbbc3e44f9550a95", "Sheaf.Paper.ConstantAdicQuotientModelRealizationExtensionIso": "6777d855cadb00454679bca8a6c21e2164494f5c", "Sheaf.Paper.ConstantAdicQuotientRealizationReflectsIso": "d6bf1f44ef4891b20cb029f21e69342c59cab688"}, "results": {}, "time": "2026-10-28T04:11:49+0800", "transitive": 0, "version": 1}
```

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
