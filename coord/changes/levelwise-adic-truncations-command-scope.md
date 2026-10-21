# Sheaf.Paper.LevelwiseAdicTruncations command scope

## Reason

The landing review classified the retained `LevelwiseAdicTruncations` delivery as an
interface change because its top-level command surface is compared by the landing
classifier (commands such as `open`, `variable`, and `attribute`).  This record
documents that surface for the rebase and makes explicit which commands are local to
this module.  The proof repair does not change any public declaration signature or
exported definition.

## Old

The module had the module-system header, the module-local `autoImplicit`,
`warn.sorry`, and instance-size options, the `CategoryTheory`/`Limits`/`Pretriangulated`/`Opposite`
opens, the `AlgebraicGeometry.Scheme` namespace variables, and the following local
registrations:

```lean
attribute [local instance 2000] reductionRingModulesHasDerivedCategory
attribute [local instance 2000] pbcTowers_hasDerivedCategory
attribute [local irreducible] completedAdicDerivedChange pbcDerivedScalarAdjunction
```

The later `open AlgebraicGeometry.ProEtale` and all namespace-scoped variables were
also module-local.  The proof-only imports were present as ordinary `import` lines.

## New

The rebased module retains the module-local options (apart from the removed
`warn.sorry` setting), opens, variables, namespace, and local registrations.  The delivery removes only unused ordinary
proof-only imports and adds private proof helpers; its public imports and all public
declarations remain unchanged.  Consequently importers receive exactly the same
module-visible command environment and declaration API after the repair.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.AdicCohomologyTorsionNormalForm` | unclaimed | Same public imports and declarations; no adaptation. |
| `Sheaf.Paper.AdicSuppliedModelFlatCriterion` | unclaimed | Same public imports and declarations; no adaptation. |
| `Sheaf.Paper.AdicTorFlatCohomology` | unclaimed | Same public imports and declarations; no adaptation. |
| `Sheaf.Paper.AdicTorFlatCriterion` | unclaimed | Same public imports and declarations; no adaptation. |
| `Sheaf.Paper.PbcConstructibleReductionCriterion` | unclaimed | Same public imports and declarations; no adaptation. |
| `Sheaf.Paper.PbcRationalTransport` | unclaimed | Same public imports and declarations; no adaptation. |
| `Sheaf.Paper.PbcUniformCompleteTriangulated` | unclaimed | Same public imports and declarations; no adaptation. |
| `Sheaf.Paper.PbcUniformLocalModelCohomology` | unclaimed | Same public imports and declarations; no adaptation. |
| `Sheaf.Paper.PbcUniformReductionCriterion` | unclaimed | Same public imports and declarations; no adaptation. |

## Status

landed 20261021T020130-L-2589201 2026-10-21 (merge of deliver/K2/Sheaf.Paper.LevelwiseAdicTruncations)
