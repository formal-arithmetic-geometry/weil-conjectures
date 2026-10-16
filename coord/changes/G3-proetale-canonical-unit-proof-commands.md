# Canonical module inverse-image unit: local proof commands

## Reason

The proof needs additional universe names, an opened Mathlib namespace, local
variables, and elaborator transparency options. The static interface detector
conservatively flags these command changes. Every added declaration is private;
the sole existing public theorem retains exactly its signature and visibility.
No library definition or target statement changes.

## Old

```lean
universe u
open CategoryTheory CategoryTheory.Limits Opposite
```

The theorem `AlgebraicGeometry.Scheme.proEtaleModuleInverseImage_canonicalUnitComparison`
had a `sorry` proof and no private helpers.

## New

```lean
universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
```

Private proof helpers use local variables and the options
`backward.isDefEq.respectTransparency` and
`backward.isDefEq.respectTransparency.types`, both set to `false`.
The public theorem now has a complete proof. The repair removes the duplicate
private `modelAbelianAdjunction_unit` helper and applies the existing Mathlib
`Adjunction.map_restrictFullyFaithful_unit_app` directly inside the comparison
proof, after mapping the uniqueness equation through the sheaf equivalence. Its statement is unchanged.
The unused proof import
`Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying` is removed.

## Users

| Module | Current holder | Effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison` | unclaimed | Its use of the unchanged public theorem is unaffected; no adaptation is needed. |

Other downstream modules see the same public declarations and signatures.
The additional opened namespace, local variables, universes and elaboration
options are confined to this module's elaboration. No module is adapted.

## Status

landed 20261016T023443-L-1242036 2026-10-16 (merge of deliver/G3/Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit)
