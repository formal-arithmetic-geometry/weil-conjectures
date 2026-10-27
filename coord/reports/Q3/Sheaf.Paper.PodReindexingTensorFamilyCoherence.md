## What changed

The assigned theorem now assembles two strictly smaller named statements. The identity/composition
component constructs the section-normalized identity and compositor and proves `Relabelling`,
`Identity`, and `Composition`. The tensor-constraint component states the remaining associator,
braiding, and unitor calculation for fixed comparisons. The parent combines these results without
changing its statement or public import. Both component proofs remain explicit named DAG holes;
there are no sorries inside definitions.

## Proved and sorry left

The parent theorem `WeilConjectures.podReindexingTensorFamilyCoherence` is proved from the two
component declarations (1 original hole closed by decomposition). Two strictly simpler sorries
are added:

- `WeilConjectures.podReindexingTensorFamilyIdentityComposition`, node
  `lem-pod-reindexing-tensor-family-identity-composition`.
- `WeilConjectures.podReindexingTensorFamilyTensorConstraints`, node
  `lem-pod-reindexing-tensor-family-tensor-constraints`.

Thus 1 upper hole is closed and 2 lower holes are added as a decomposition. The assigned module
contains no remaining `sorry`; each new module contains exactly its named theorem `sorry`.

## No longer needed

No existing imports or declared dependencies were removed. The original single proof step is
replaced by the two component nodes, which retain its section-map, quotient-generator, Roos,
and tensor-generator route. No unrelated module is pruned.

## Where the brief, the DAG or earlier work was wrong

The original node bundled construction of the section-normalized identity/composition maps with
the independent tensor associator, braiding, and unitor calculation. Those are separate strict
subarguments with different inputs: the tensor constraints require the identity and compositor
as fixed data. The delivery records both subarguments as named statements and combines them by a
real Lean proof. No target statement, definition, or unit-level route was changed.

## New nodes

`lem-pod-reindexing-tensor-family-identity-composition` records the existence of the fixed
section-normalized identity/composition comparisons and their reduction, limit, and completed
tensor laws. Its Lean declaration is in
`Sheaf.Paper.PodReindexingTensorFamilyIdentityComposition`.

`lem-pod-reindexing-tensor-family-tensor-constraints` records the associator, signed braiding,
and unitor equations for a fixed family. Its Lean declaration is in
`Sheaf.Paper.PodReindexingTensorFamilyTensorConstraints`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingTensorFamilyCoherence": "ac65d88a31d79516bca48071e55603d49f48444e", "Sheaf.Paper.PodReindexingTensorFamilyIdentityComposition": "126b4f2b3404ea21accdef8edbf4a378b3ea57c2", "Sheaf.Paper.PodReindexingTensorFamilyTensorConstraints": "bc281e416890df43e0665b4cd70b0cf8429206b8"}, "results": {}, "time": "2026-10-28T07:07:54+0800", "transitive": 0, "version": 1}
```

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
