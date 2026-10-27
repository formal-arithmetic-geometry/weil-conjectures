## What changed

The target theorem in `Sheaf.Paper.SystemDirectImageRoosPresentation` is reduced to two strictly smaller public interfaces. `SystemDirectImageRoosExistence` isolates existence of the product, Roos object, and total-limit comparison. `SystemDirectImageRoosEvaluation` isolates the finite evaluation isomorphisms and their projection equations. The target imports both modules and combines their conclusions. The two lower interfaces retain the paper's single-resolution and projection-normalization proof obligations as named stage-3 statements.

## Proved and sorry left

The target declaration `WeilConjectures.systemDirectImage_roosPresentation` is reduced and compiles once its two strict substatements are available. Two strictly smaller proof obligations remain as named `sorry`s:

- `WeilConjectures.systemDirectImage_roosExistence` in `stage3-weil-system-direct-image-roos-existence`.
- `WeilConjectures.systemDirectImage_roosEvaluation` in `stage3-weil-system-direct-image-roos-evaluation`.

No definition contains `sorry`.

## No longer needed

No existing proof dependency is pruned. The target's former monolithic proof steps are represented by the two new interfaces; all original imports remain available through the target and split modules.

## Where the brief, the DAG or earlier work was wrong

The original DAG assigned a three-step construction requiring simultaneous K-injective evaluation, transition transport, and Roos-limit transport as one theorem. The available Lean declarations expose these as separate categorical interfaces, so keeping them as one hole made the proof obligation too large to state and review effectively. The decomposition preserves the exact target statement and the unit route.

## New nodes

`stage3-weil-system-direct-image-roos-existence` records the existence and total-limit comparison substatement.

`stage3-weil-system-direct-image-roos-evaluation` records the finite evaluation and projection compatibility substatement.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.SystemDirectImageRoosEvaluation": "48bda4884070da4580f3ccf715ab32c34a6d9190", "Sheaf.Paper.SystemDirectImageRoosExistence": "c4d199ebfb455f4348f86642110a9f881f350675", "Sheaf.Paper.SystemDirectImageRoosPresentation": "5618a40ae636091c3f08be3eeada991fbf519eb3"}, "results": {"Sheaf.Paper.SystemDirectImageEffectivity": {"hash": "67a63117390570e5a17c38367e23e477adbcce36", "status": "OK"}}, "seconds": 274, "time": "2026-10-27T23:48:12+0800", "transitive": 0, "version": 1}
```

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
