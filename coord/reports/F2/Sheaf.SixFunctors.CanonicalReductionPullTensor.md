## What changed

Filled `WeilConjectures.GeneratorReduction.canonicalReductionPullTensor` by applying
`WeilConjectures.IntegralSystemRealization.canonicalReductionTensorPull` to the
underlying system, realization, and ringed models and taking equality symmetry.
Added the proof-only import `Sheaf.SixFunctors.CanonicalReductionTensorPull`. Updated
`lem-sf-canonical-reduction-pull-tensor` so its proof and proof dependencies record
this direct route.

## Proved and sorry left

Closed the sole hole, `WeilConjectures.GeneratorReduction.canonicalReductionPullTensor`.
The item module adds no `sorry` and leaves none in the item.

## No longer needed

No imports were removed. The original planned proof dependencies
`lem-coef-derived-system-evaluation-calculus`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, and
`lem-weil-pbc-site-derived-tensor-descent` are not needed for the direct symmetry
proof and were removed from this node's `proof_deps`; the statement dependencies
remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The detailed representative-level proof plan was unnecessary for this statement:
`canonicalReductionTensorPull` already proves the same equality with the two sides
reversed, so symmetry closes the target directly. No statement or definition was
changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CanonicalReductionPullTensor": "fb2e06185da6840423232d9b8e94a0534d1f6532"}, "results": {}, "time": "2026-10-27T23:23:42+0800", "transitive": 0, "version": 1}
```

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
