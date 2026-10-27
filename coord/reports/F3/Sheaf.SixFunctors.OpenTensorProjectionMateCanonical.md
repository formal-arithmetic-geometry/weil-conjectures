## What changed

Updated the existing `STATEMENT-DISPUTED` comment on
`WeilConjectures.CoefSupportOpenTensor.openTensorProjection_mate_canonical` with
an explicit componentwise counterexample check. No declaration signature,
imports, definitions, or DAG records changed. The module compiles unchanged
apart from this explanatory marker and retains its one named theorem `sorry`.

## Proved and sorry left

No holes were closed. The existing `sorry` in
`WeilConjectures.CoefSupportOpenTensor.openTensorProjection_mate_canonical`
remains, attached to `lem-sf-open-tensor-projection-mate-canonical`. No new
`sorry` declarations were added.

## No longer needed

None. Both public imports remain needed by the theorem's statement and data.
No DAG nodes or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

`STATEMENT-DISPUTED`: the theorem is false as written. A
`RingedDerivedTensorComparison` is only a family of isomorphisms indexed by
pairs and a one-flat proof; it has no naturality or normalization law. Starting
with any valid family, compose the ambient component at
`(((F.mapHomologicalComplex (.up ℤ)).obj C), P)` with a nontrivial automorphism
(for example `-𝟙` over a characteristic-zero coefficient site). This preserves
all listed hypotheses, including `hordinary`, while changing the displayed
right-hand side and leaving the left-hand side unchanged. The missing
`ambientBoth`/`openBoth` and naturality hypotheses occur only downstream.
A valid repair needs those coherence assumptions or canonical normalized
comparison families. The existing marker is retained and strengthened.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenTensorProjectionMateCanonical": "f3fbee26702c9590ecb8cce352875a5399b063b3"}, "results": {}, "time": "2026-10-28T05:06:39+0800", "transitive": 0, "version": 1}
```

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
