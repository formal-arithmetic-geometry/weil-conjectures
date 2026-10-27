## What changed
Filled the ordinary and signed-total scalar tensor construction already present in the item. Decomposed the remaining derived `scalarTensor_existsUnique` obligation into named existence and uniqueness theorems, then proved the original theorem by combining them and selecting the unique comparison. Updated the item node proof route and added two intermediate DAG nodes.

## Proved and sorry left
Closed the original `WeilConjectures.PurCompactSupport.scalarTensor_existsUnique` sorry by a real proof from the two intermediate statements. Two strictly simpler intermediate sorries remain: `scalarTensor_exists` (`new-sf-scalar-tensor-existence`) and `scalarTensor_unique` (`new-sf-scalar-tensor-uniqueness`). The module therefore closes 1 of its 1 original sorry and adds 2 named split-off holes.

## No longer needed
No imports were removed. The original bundled derived-descent obligation is no longer left as an anonymous hole; its existence and uniqueness parts are represented by the two new nodes.

## Where the brief, the DAG or earlier work was wrong
The prior node treated the derived descent obligation as a single theorem. The proof can be made into Lean with a genuine decomposition into existence and uniqueness, and `scalarTensor_existsUnique` combines these parts without restating its own statement.

## New nodes
`new-sf-scalar-tensor-existence` records existence of the normalized derived comparison. `new-sf-scalar-tensor-uniqueness` records uniqueness of two normalized comparisons. Both are strictly simpler than the original ExistsUnique obligation and are stated in the item module with complete source and proof descriptions.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralCompactSupportScalarTensor": "6827afed17ebf5b2894ae42b90e35fac0f5330b2"}, "results": {"Sheaf.Paper.IntegralCompactSupportCoefficientComparison": {"hash": "512a53a6ba71feaf0c60b3c8b13a5a25de22a912", "status": "OK"}}, "seconds": 104, "time": "2026-10-28T05:17:25+0800", "transitive": 0, "version": 1}
```

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
