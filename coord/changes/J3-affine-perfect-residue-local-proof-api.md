# AlgebraicGeometry.Scheme.affine_perfect_residue_model_naturality

## Reason

Restore the quarantined module against the adopted-source affine pullback API.
The old local generic additivity instance is unnecessary: the proof calls additivity
explicitly where needed and uses the existing zero-preservation API for affine
sheafification. Local irreducibility guards keep the affine-chart definitions behind
those APIs during elaboration. The repaired module compiles cleanly in 27.4 seconds.

Preflight classifies the changed file-level attribute commands as a possible change
to what importers see and requires this record. Both commands are explicitly local;
no global attribute, public import, public definition, or public theorem signature
changes. The four new private categorical helpers are fully constructed/proved from
Mathlib and occur only in proof bodies. Invertibility evidence is passed explicitly to the abstract comparisons, and
the main proof uses the comparison APIs without transparency overrides. There are no
consumer adaptations.

## Old

The archived module contains this local attribute command:

```lean
attribute [local instance] Functor.additive_of_preserves_binary_products
```

## New

Remove that local instance command. Before the main theorem, add exactly:

```lean
attribute [local irreducible] Modules.overEquiv affinePerfectSheafification openResiduePoint
```

The public theorem signature and the three public imports remain verbatim. No definition
body changes. The local transparency options on the new helpers affect only their own
proof elaboration.

## Users

`tools/downstream.py` with `--allow-missing --uses` reports zero live consumers, because
the item and all its downstream consumers are quarantined. A source import-graph scan
including `quarantine/` finds the consumers below. The direct consumer's use of the
unchanged theorem was read in full. All rows preserve the same interface, so this
repair does not force an edit to any consumer or change the meaning of any target.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineResidueModelNaturality | unclaimed | Quarantined direct theorem user; signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreNaturality | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridge | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridgeCore | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonTargets | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison | unclaimed | Quarantined transitive consumer; no interface change or adaptation. |

## Status

landed 20261020T211740-L-3496516 2026-10-20 (merge of deliver/J3/Sheaf.AlgebraicGeometry.AffinePerfectResidueModelNaturality)
