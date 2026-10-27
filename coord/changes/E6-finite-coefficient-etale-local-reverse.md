# AlgebraicGeometry.Scheme.finiteCoefficient_etaleLocal_encoding_reverse

## Reason

The proof activates the existing AsSmall equivalence/density facts as local
instances and prevents unfolding of the large scalar-extension witness and its
adjunction while checking its private helper. These commands are local to the
item module. The source interface checker records top-level commands, including
local attributes, so this record makes their scope explicit. All existing
public declaration signatures, definitions, public imports, and exported
attributes remain identical. Added imports are proof-only.

## Old

```lean
attribute [local instance] finitePerfectModelsAbLocallyBijective
```

The theorem's body was `:= by sorry`.

## New

```lean
attribute [local instance] finitePerfectModelsAbLocallyBijective

attribute [local instance] ProFiniteModels.asSmallDownEquivalence
  ProFiniteModels.asSmallUpEquivalence ProFiniteModels.asSmallDense
  ProFiniteModels.asSmallUpDense
```

Before the private scalar-model reflection helper:

```lean
attribute [local irreducible] completedAdicChangeData pbcScalarAdjunction
```

The theorem now has a complete proof and three proved private helpers. No
exported instance or attribute is added or removed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteCoefficientEtaleLocalEncoding | unclaimed in shared claim snapshot | Same public statement and imports; proof-local attributes have no effect on importers. |

## Status

landed 20261027T180547-L-3875902 2026-10-27 (merge of deliver/E6/Sheaf.Paper.FiniteCoefficientEtaleLocalEncodingReverse)
