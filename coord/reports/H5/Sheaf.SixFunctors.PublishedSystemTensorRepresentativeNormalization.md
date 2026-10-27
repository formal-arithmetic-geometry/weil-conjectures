## What changed

The item module now proves `publishedSystemTransportedTensor_normalized` by combining two
strictly smaller named steps in the same module. The flat representative rectangle and the
K-flat descent equality are recorded as public intermediate theorems with their own DAG nodes.
The final theorem rewrites by the descent equality and applies the existing defining equation
for `pullbackTensorSystemComparison`.

## Proved and sorry left

The item theorem `publishedSystemTransportedTensor_normalized` is proved. Two strictly simpler
intermediate statements remain sorry: `publishedSystemTransportedTensor_normalized_flat`
(flat-term representatives only, node
`lem-sf-published-system-tensor-identification-representative-flat`) and
`publishedSystemTransportedTensor_eq_of_flat_normalized` (the K-flat descent step, node
`lem-sf-published-system-tensor-identification-representative-descent`). The original item had
one sorry; this delivery closes it and adds two named split-off sorries.

## No longer needed

No proof dependency imports were removed. The original four dependency nodes are used by the
flat representative substep; the item theorem itself uses only the two new intermediate nodes
and the existing uniqueness specification.

## Where the brief, the DAG or earlier work was wrong

The one-step DAG proof plan omitted the distinction between the flat-term representatives used
by the ambient tensor model and the arbitrary independent K-flat complexes quantified by the
item. The delivery makes this distinction explicit through a flat representative statement and
a separate descent statement.

## New nodes

`lem-sf-published-system-tensor-identification-representative-flat` records the normalized
rectangle on flat-term K-flat representatives. `lem-sf-published-system-tensor-identification-representative-descent`
records the tensor-model rigidity and localization descent from those representatives to the
comparison isomorphism equality. Both node files are under `dag/nodes/sec-six-functors/`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.PublishedSystemTensorRepresentativeNormalization": "7c63772f1808be4759e266e3e5c7f67ad3766414"}, "results": {"Sheaf.SixFunctors.PublishedSystemTensorIdentification": {"hash": "3c612b614772329438b649508249ab2fbe797b1c", "status": "OK"}}, "seconds": 9, "time": "2026-10-28T04:44:57+0800", "transitive": 0, "version": 1}
```

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
