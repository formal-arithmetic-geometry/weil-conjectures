## What changed

The assigned theorem now composes two explicit comparison interfaces. I added
`FiniteModelConstantScalarExtensionDerivedChangeBridge` for the comparison between the
selected completed derived change and lifted constant realization, and
`FiniteModelConstantScalarExtensionLiftComparison` for the lifted balanced-tensor
comparison. The assigned module imports these proof-only interfaces and composes their
isomorphisms. The item theorem itself is proved with no remaining `sorry`.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.finiteModel_constantScalarExtension_core` (one hole
closed). The two strictly simpler interface theorems
`finiteModel_constantScalarExtension_derivedChangeBridge` and
`finiteModel_constantScalarExtension_liftComparison` remain as named `sorry` obligations,
with nodes `lem-weil-pbc-finite-model-derived-change-bridge` and
`lem-weil-pbc-finite-model-lift-comparison` respectively.

## No longer needed

The original planned proof dependencies `lem-pc-large-filtered-free-resolution`,
`lem-pc-filtered-free-kprojective`, and `def-weil-pbc-intrinsic-koszul-completion` are
not used by the composed interface proof. No imports were removed from the published
module; the proof-only imports are exactly the two new interface modules.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan expanded the filtered-free resolution argument but omitted
the existing derived constant-realization interface and the required completed-change
bridge. The revised node records the two actual intermediate interfaces used by the Lean
proof.

## New nodes

`lem-weil-pbc-finite-model-derived-change-bridge` is the completed derived-change bridge;
its Lean declaration is in
`lean/Sheaf/Paper/FiniteModelConstantScalarExtensionDerivedChangeBridge.lean`.

`lem-weil-pbc-finite-model-lift-comparison` is the lifted balanced-tensor comparison;
its Lean declaration is in
`lean/Sheaf/Paper/FiniteModelConstantScalarExtensionLiftComparison.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteModelConstantScalarExtensionCore": "25d07cb549818627a29bd4adcf31e28e722319a3", "Sheaf.Paper.FiniteModelConstantScalarExtensionDerivedChangeBridge": "23952710582ac581d7e526cc6992022dc0f15ee0", "Sheaf.Paper.FiniteModelConstantScalarExtensionLiftComparison": "ec032117f7a6520044d30d67d45c6817ff0abac3"}, "results": {}, "time": "2026-10-28T04:17:11+0800", "transitive": 0, "version": 1}
```

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
