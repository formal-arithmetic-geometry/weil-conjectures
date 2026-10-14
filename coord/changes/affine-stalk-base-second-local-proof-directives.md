# Sheaf.Algebra.Homology.AffineStalkBaseSecondLocalizationComparison proof directives

## Reason

The delivery checker classifies changed `attribute` commands as interface changes.
These attributes are explicitly local: they supply the tensor-product right-algebra
instance and keep large chosen-model definitions abstract while elaborating this
file's proofs. The theorem-specific heartbeat setting permits the necessary scalar
instance elaboration. Neither command changes an imported module's instances,
reducibility, options, declarations, or public signatures. The completed file compiles
without warnings in 33.7 seconds, within the unchanged 60-second wall-clock limit.

No definition or intermediate statement changes. The assigned public theorem's
signature is byte-for-byte identical to the original. Consequently no target's
meaning changes and no target-statement review or downstream adaptation is needed.

## Old

The original surrounding commands, verbatim:

```lean
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
```

The public theorem originally had no declaration-local heartbeat setting.

## New

```lean
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local irreducible] AlgebraicGeometry.SingleComplexBaseChange.tensorMap
  AlgebraicGeometry.SingleComplexBaseChange.cohomologyModel
  ModuleCat.baseDerivedTensorCohomologyModel
noncomputable section
```

Immediately before the unchanged public theorem docstring:

```lean
set_option maxHeartbeats 600000 in
-- Comparing affine and scheme stalk presentations needs substantial instance elaboration.
```

The additional coefficient-complex definition is private and irreducible; its
unit-tensor equation is proved explicitly. All other new helpers are private and
proved. The two new imports are proof-only imports.

## Users

The downstream textual search for the assigned public theorem finds its own
module and the following caller. No caller sees the local directives, and every
existing signature and visibility remains identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineStalkBaseSecondLocalizationComparison | Y2 | Local elaboration directives and a completed proof; unchanged public interface. |
| Sheaf.Algebra.Homology.AffineDirectLocalizedTensorSquareCore | unclaimed | Unaffected: the same theorem signature and public imports remain available. |

No module is adapted by this delivery.

## Status

landed 20261014T101748-L-1177452 2026-10-14 (merge of deliver/Y2/Sheaf.Algebra.Homology.AffineStalkBaseSecondLocalizationComparison)
