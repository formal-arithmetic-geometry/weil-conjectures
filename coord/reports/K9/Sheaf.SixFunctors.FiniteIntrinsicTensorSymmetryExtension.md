## What changed

Replaced the sole hole in
`WeilConjectures.IntegralVerdier.finiteIntrinsicTensorSymmetry_extension`
by the natural-transformation extension argument. The two composites are natural:
the intrinsic interchange uses `hs`, and the fixed interchange is obtained by
flipping and uncurrying `b.inv`. Their restrictions agree by `hres`.
`finiteScalarRepresentativesFullyFaithful` then implies equality on every derived pair.
The theorem signature and all public imports are unchanged. Updated the item's
DAG proof and proof dependencies to match this argument. A declaration-local
unused-variable linter option preserves the published `hb`, `hP`, and `hQ` binders.
The complete proof compiled in 16.6 seconds before that linter-only cleanup;
the delivery performs the final clean compile and axiom probe.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.IntegralVerdier.finiteIntrinsicTensorSymmetry_extension`
(node `lem-sf-finite-intrinsic-tensor-symmetry-extension`).
No holes added, no split-off statements, and no sorry remains in the item module.

## No longer needed

The extension proof does not use
`lem-sf-finite-intrinsic-tensor-symmetry-resolving` or its theorem
`finiteIntrinsicTensorSymmetry_resolving`; removed it from `proof_deps`.
Its public import is retained because the direct importer
`Sheaf.SixFunctors.FiniteIntrinsicTensorSymmetry` uses that exported theorem to
supply `hres`. Thus this is pruning of the extension's proof dependency only;
that module and node remain needed by the parent, and no module is withdrawn.
The normalization hypothesis `hb` is unnecessary for the extension argument,
but its existing binder is preserved.

## Where the brief, the DAG or earlier work was wrong

The proof plan listed the representative symmetry calculation as an extension
proof dependency even though its result is already the hypothesis `hres`.
The fully faithful restriction theorem and ordinary functor-category operations
suffice, so this obligation requires no further split.
The node's source path under `sec-six-functors` does not exist in the current
blueprint checkout: the corresponding unit is under `sec-six-functors-basics`.
The unit record has no realized steps to bypass; the localization extension route
is preserved.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.FiniteIntrinsicTensorSymmetryExtension": "a136b407c96ca7006d9bae43ec4a62506117d42b"}, "results": {}, "time": "2026-10-28T12:03:46+0800", "transitive": 0, "version": 1}
```

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
