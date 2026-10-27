## What changed

Added the proof-only module `Sheaf.Paper.FiniteIntrinsicTensorComponent`, whose
pointwise comparison theorem isolates the simultaneous flat K-flat representative
construction from the family assembly. The assigned theorem now applies that pointwise
comparison at each `SixFunctorSpace` and assembles the chosen isomorphisms with a genuine
function construction. Its public statement and all binders are unchanged.

The component module imports the three declarations named by the original DAG plan:
the pro-etale intrinsic tensor comparison, the intrinsic realization of total tensor
complexes, and the independent-coefficient K-flat resolution theorem. The parent module
imports only the component for its proof.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralProjectionReduction.finiteIntrinsicTensorRealization`.
The proof is the family assembly from the pointwise theorem.

One strictly simpler hole remains in
`WeilConjectures.IntegralProjectionReduction.finiteIntrinsicTensorRealization_component`,
node `lem-sf-finite-intrinsic-tensor-component`. It is the fixed-space comparison used by
the original construction plan. No sorry occurs in a definition or private helper.

## No longer needed

The assigned module no longer directly imports the three low-level construction modules;
they remain necessary through `FiniteIntrinsicTensorComponent`, where their declarations
are the proof dependencies of the pointwise construction. No module or DAG unit step is
withdrawn, and no adopted source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The original item proof plan bundled the pointwise representative comparison and the
assembly over all ambient spaces into one admitted theorem. The family statement only
needs the strictly simpler pointwise existence statement plus choice, so the construction
has been split at that boundary. The target statement is unchanged.

## New nodes

`lem-sf-finite-intrinsic-tensor-component` records the pointwise finite intrinsic-to-fixed
tensor comparison and its representative-level proof plan. The item node now records the
assembly step and depends on this node.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteIntrinsicTensorComponent": "9ddf49c17f54f646112c59dc96fb0ed4d163bf48", "Sheaf.Paper.FiniteIntrinsicTensorRealization": "c6dab40782ee54614459be8d3bc0c9bb401b60ae"}, "results": {}, "time": "2026-10-28T04:17:31+0800", "transitive": 0, "version": 1}
```

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
