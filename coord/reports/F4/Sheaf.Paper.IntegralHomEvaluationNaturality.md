## What changed

Added the private proof import `Sheaf.Paper.IntegralHomEvaluationTransport` and replaced the
original hole in `WeilConjectures.IntegralHom.evaluation_naturality` by a real categorical
reduction. The proof obtains a native closed structure and an exchanged tensor comparison,
then applies naturality of its transported counit.

The new transport module defines `swapTensor` and `transportedCounit`, and introduces two
named intermediate theorems. Their statements isolate the representative comparison and
the formal naturality calculation.

## Proved and sorry left

The original declaration `WeilConjectures.IntegralHom.evaluation_naturality` is proved.

Two strictly lower obligations are split off and remain as `sorry`:

- `WeilConjectures.IntegralHom.tensorPresentation_counit_transport`, node
  `lem-sf-integral-hom-evaluation-transport`.
- `WeilConjectures.IntegralHom.transportedCounit_naturality`, node
  `lem-sf-integral-hom-evaluation-transport-naturality`.

Holes closed: 1. Holes added: 2. This is a decomposition of the representative comparison
and its formal transport, with the parent theorem itself closed.

## No longer needed

No existing public imports or DAG dependencies were removed. The proof uses the native closed
structure, its evaluation naturality, and the supplied presentation. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier proof plan bundled two distinct tasks: comparing an arbitrary supplied
TensorPresentation with native closed evaluation, and proving naturality after that comparison.
The latter is a short categorical step once the former is available, so the obligations are now
split at that boundary. No statement was weakened and no target definition was changed.

## New nodes

`lem-sf-integral-hom-evaluation-transport` records the K-flat/full-faithfulness comparison of a
supplied normalized presentation with the exchanged native tensor and the resulting counit
comparison. `lem-sf-integral-hom-evaluation-transport-naturality` records the formal consequence
of that comparison and native `CoefficientClosedStructure.evaluation_naturality`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralHomEvaluationNaturality": "0eb08460cfcad9a63937cab759f258783e9b8945", "Sheaf.Paper.IntegralHomEvaluationTransport": "1c5bffef774a6a4d6836802af9aa615b31ab9b05"}, "results": {}, "time": "2026-10-28T07:00:37+0800", "transitive": 0, "version": 1}
```

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
