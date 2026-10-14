# tensorIdealSectionMultiply_coefficient_comparison: local proof settings

## Reason

The proof compares explicit tensor isomorphism composites. During rewriting, Lean otherwise
unfolds the ideal module into its categorical kernel and unfolds the pullback comparison
constructions, causing a deterministic heartbeat timeout while matching `block_append`.
Local irreducibility keeps those data constructions abstract; the proof unfolds only their
named defining equations. The static interface checker classifies changed top-level local
attribute commands and proof-elaboration options as an interface change, so this record
explicitly documents their scope and effect.

No existing definition, statement, signature, visibility, or public import changes.
These attributes are local to this module's namespace and end with it. The options control
elaboration in this module, and do not become settings for an importing module. No
adaptation of another module is needed.

## Old

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] canonicalTensorBoundaryComparisons
```

## New

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensorPullback boundaryPullbackComparison
  canonicalTensorBoundaryComparisons tensorIdealSectionMultiply boundarySectionDegreeIso
  boundaryCoefficientDegreeIso boundaryPullbackPowIso boundaryTensorPowIso
  tensorPowAddIso tensorPowMulIso Scheme.IdealSheafData.toModules
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.TensorIdealSectionCoefficientComparison
--uses tensorIdealSectionMultiply_coefficient_comparison` reports 170 downstream modules
and the two textual references below, including the item itself. Every downstream statement
keeps its original meaning: the public theorem has exactly its original type, public imports
stay identical, and these proof settings are local.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.TensorIdealSectionCoefficientComparison | E4 | Proof elaboration only; theorem signature identical. |
| Sheaf.AlgebraicGeometry.TensorCoefficientActionOnSummand | unclaimed in this checkout | No effect; its theorem application and imported interface stay identical. |

No other module is edited or requires a forced adaptation. The explicit use in
`TensorCoefficientActionOnSummand` continues to take exactly the original j, L, hI, n,
D, hD, e, f, and h arguments.

## Status

landed 20261014T054050-L-2106170 2026-10-14 (merge of deliver/E4/Sheaf.AlgebraicGeometry.TensorIdealSectionCoefficientComparison)
