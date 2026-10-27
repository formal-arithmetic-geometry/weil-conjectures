## What changed

Proved `WeilConjectures.publishedSystemTensorIdentification` by defining the transported ambient tensor comparison, identifying it with the unique pullback tensor system comparison, and applying a proved categorical component cancellation lemma. Added a split-off representative normalization theorem in `Sheaf.SixFunctors.PublishedSystemTensorRepresentativeNormalization`.

## Proved and sorry left

Closed the target sorry in `publishedSystemTensorIdentification`. The split-off theorem `publishedSystemTransportedTensor_normalized` remains one sorry; it is the strict chain-level representative rectangle needed by the uniqueness argument and is recorded as a new DAG node.

## No longer needed

No imports or declared dependencies were removed. The direct target proof uses only the transported comparison, its uniqueness theorem, and the categorical transport lemma; the chain-level work is isolated in the new representative-normalization node.

## Where the brief, the DAG or earlier work was wrong

The original module's two-page proof plan requires a chain-level representative normalization that cannot be discharged from the available declarations in this item. The item is therefore reduced to that strictly smaller representative theorem plus a complete categorical argument. The current global build record also reports a pre-existing bad import in the quarantined upstream coefficient-change cluster; direct sandbox compilation of this delivery succeeds.

## New nodes

`lem-sf-published-system-tensor-identification-representative` records `publishedSystemTransportedTensor_normalized` and its Stacks sources, dependencies, and proof plan.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.PublishedSystemTensorIdentification": "3c612b614772329438b649508249ab2fbe797b1c", "Sheaf.SixFunctors.PublishedSystemTensorRepresentativeNormalization": "a20fa0a34ac18d0d201311bd893755c722b43102"}, "results": {}, "time": "2026-10-28T01:22:59+0800", "transitive": 0, "version": 1}
```

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
