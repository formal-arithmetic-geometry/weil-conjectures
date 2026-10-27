## What changed

Copied the assigned module into the sandbox and marked the theorem
`openTensorProjection_mate_canonical` as `STATEMENT-DISPUTED`. No declarations,
imports, or signatures were changed. The module compiles with its existing single
`sorry`.

The issue is that `ambientModel` and `openModel` are arbitrary one-flat
comparison families. The theorem supplies neither naturality nor agreement with
the simultaneous models for them.

## Proved and sorry left

No holes were closed. The existing `sorry` in
`WeilConjectures.CoefSupportOpenTensor.openTensorProjection_mate_canonical`
remains; it is the node `lem-sf-open-tensor-projection-mate-canonical`.
No new `sorry` declarations were added.

## No longer needed

None. The two public imports remain required by the declaration and its data.
No DAG nodes or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

The theorem statement is false as written. `RingedDerivedTensorComparison` is
just a family of isomorphisms indexed by pairs and a one-flat proof; it carries
no naturality or normalization law. Starting from any valid comparison family,
modify the ambient component at the single pair
`(((F.mapHomologicalComplex (.up ℤ)).obj C), P)` by composing with a nontrivial
automorphism of its source or target (for example `-𝟙` over a characteristic-zero
coefficient site). This still has exactly the required
`RingedDerivedTensorComparison` type and does not affect `hordinary`, `D`, or the
open component. The displayed right-hand side changes, while the left-hand side
is unchanged, so the asserted equality cannot follow from the listed hypotheses.
The missing `ambientBoth`/`openBoth` and naturality hypotheses appear only in the
downstream resolving/descent statements. A valid repair must add the required
normalization/naturality assumptions or replace the arbitrary families by the
canonical normalized comparisons.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenTensorProjectionMateCanonical": "458cbc6f991664b5f2541bac939dd6fb61f65890"}, "results": {}, "time": "2026-10-28T03:28:35+0800", "transitive": 0, "version": 1}
```

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
