## What changed

The target theorem now assembles `ConstructionMaps` from two strictly smaller component
statements.  `finiteScalarMapsCore_exists` supplies the finite-subcategory maps, their
normalization and counit equation, and both shift equations.  `finiteScalarMapsEtale_exists`
supplies the ambient ordinary-etale `EtaleMates` package.  The target constructor combines
these components.  All three sandbox modules compile in import order.

## Proved and sorry left

`finiteScalarMaps_exists` is proved by the constructor assembly.  Two component theorem
proofs remain as named, documented `sorry`s:

* `finiteScalarMapsCore_exists` in `ExceptionalFiniteScalarMapsCore.lean`;
* `finiteScalarMapsEtale_exists` in `ExceptionalFiniteScalarMapsEtale.lean`.

Thus one target hole was closed and two strictly smaller holes were split off.

## No longer needed

No imports or declared mathematical dependencies were pruned.  The three original proof
dependencies remain attached to the two component nodes, where they are the sources of the
remaining component obligations.

## Where the brief, the DAG or earlier work was wrong

The original one-step DAG proof described the finite-subcategory transport and the ambient
ordinary-etale mate construction together, although the Lean target is a constructor with
these independent components.  Splitting those components makes the constructor proof
checkable without changing its statement.

## New nodes

* `lem-sf-exceptional-finite-scalar-maps-core` /
  `Sheaf.Paper.ExceptionalFiniteScalarMapsCore`;
* `lem-sf-exceptional-finite-scalar-maps-etale` /
  `Sheaf.Paper.ExceptionalFiniteScalarMapsEtale`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalFiniteScalarMaps": "b92ef4e87bca812aa26b7fee8dd6dfc8f7f87de6", "Sheaf.Paper.ExceptionalFiniteScalarMapsCore": "669a5a1c175d0584f39fcec578caa1d4ba082ff8", "Sheaf.Paper.ExceptionalFiniteScalarMapsEtale": "c6414de55eb20e84998ed25c12c3d59eb560b64b"}, "results": {}, "time": "2026-10-28T03:30:46+0800", "transitive": 0, "version": 1}
```

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
