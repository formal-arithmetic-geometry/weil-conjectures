## What changed

Reduced `finiteIntrinsicTensorSymmetry` to two named substeps and proved the target by composing them. Added the resolving-representative and derived-extension modules; both compile with their documented theorem holes.

## Proved and sorry left

Closed the original `finiteIntrinsicTensorSymmetry` hole by applying the two decomposition theorems. Added `finiteIntrinsicTensorSymmetry_resolving` and `finiteIntrinsicTensorSymmetry_extension`, each left as a named theorem with `sorry` because the pure-tensor calculation and the fully faithful extension require the remaining long categorical arguments.

## No longer needed

The original proof plan's direct use of the lower representative-data, complex-constraint, and resolution nodes is now mediated by the two split-off statements. No imports were removed; all cited dependencies remain needed by the split statements.

## Where the brief, the DAG or earlier work was wrong

The original item combined the representative computation and localization extension into one theorem, although the available declarations only support these as separate categorical steps. The split statements are strict restrictions: one is only on flat-term K-flat representatives, and the other takes that restricted equality as an input.

## New nodes

- `lem-sf-finite-intrinsic-tensor-symmetry-resolving`
- `lem-sf-finite-intrinsic-tensor-symmetry-extension`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.FiniteIntrinsicTensorSymmetry": "725d0bc8686fb680a169e8e6a974ea9148b13bb7", "Sheaf.SixFunctors.FiniteIntrinsicTensorSymmetryExtension": "f12e2cb63a1a7f3d4af22e5ef3027f14df4fd68e", "Sheaf.SixFunctors.FiniteIntrinsicTensorSymmetryResolving": "ea70120a4f4644d72812819c4ac5778954d93928"}, "results": {}, "time": "2026-10-28T09:53:39+0800", "transitive": 0, "version": 1}
```

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
