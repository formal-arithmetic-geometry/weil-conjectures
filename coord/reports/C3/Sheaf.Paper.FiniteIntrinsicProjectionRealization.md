## What changed

Restored the two strictly smaller proof components from the prior decomposition: `FiniteIntrinsicTensorRealization`
constructs the ambient tensor comparison, and `FiniteIntrinsicProjectionCompatibility` proves the projection
identity for a supplied comparison. The item theorem now obtains the comparison and combines the two component
theorems. Both component modules are proof-only imports. The full current `SystemProjectionFormulaCoherence`
module is retained unchanged.

## Proved and sorry left

The item theorem `finiteIntrinsicProjectionRealization` is proved by combining the two component statements.
The two split component theorems remain named `finiteIntrinsicTensorRealization`
(`new-sf-finite-intrinsic-tensor-realization`) and `finiteIntrinsicProjectionCompatibility`
(`new-sf-finite-intrinsic-projection-compatibility`); each is a public theorem with a documented source and
proof plan. No definition contains `sorry`.

## No longer needed

No prior proof dependency is removed. The parent proof uses exactly the two new component modules. The original
coherence module is not changed or pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned rework row records the earlier stale bad-import build. The current imported modules compile, and the
item's earlier proof was already reduced into these two strict components in the prior delivery history. I restored
that reduction without the prior delivery's unrelated truncation of `SystemProjectionFormulaCoherence`.

## Second reading by C3

Direct worker second reading is not part of the current stage-3 protocol. The reduction was checked by compiling all
three delivered modules in dependency order; the parent statement and unit route remain unchanged.

## New nodes

`new-sf-finite-intrinsic-tensor-realization` records the tensor-comparison construction and its remaining named
`sorry`. `new-sf-finite-intrinsic-projection-compatibility` records the projection compatibility equation under a
supplied comparison and its remaining named `sorry`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteIntrinsicProjectionCompatibility": "449114af9b636ce8912eaa61c5f05af91914bf87", "Sheaf.Paper.FiniteIntrinsicProjectionRealization": "183faf7f2d752f235aed814f1e607ee3f14b03aa", "Sheaf.Paper.FiniteIntrinsicTensorRealization": "130e987229c63f831c30aa8f2bdcbf8e742dfd7c"}, "results": {}, "time": "2026-10-28T00:47:38+0800", "transitive": 0, "version": 1}
```
