# AlgebraicGeometry.Scheme.Modules.coherent_ideal_patching_generic_embedding_core

## Reason

The finite-sum proof needs biproduct instances from finite products and the preservation
of biproducts by a functor preserving products. Two local instance attributes provide
these instances inside the module. Preflight conservatively treats added commands as
an interface change and requires this record. No existing public signature or definition
changes. Stalk finite-limit preservation is a private theorem; it is installed only as a
local instance inside the private stalk-sum proof, not as a new global instance.

## Old

The original file contains no extra scoped proof commands between
`namespace AlgebraicGeometry.Scheme.Modules` and its theorem.

## New

```
noncomputable section

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] preservesBiproduct_of_preservesProduct
```

The section ends before the existing namespace ends. These local attributes assist
elaboration of private helpers and the theorem proof. The theorem has two individually
scoped elaboration options (`backward.isDefEq.respectTransparency false` and
`backward.defeqAttrib.useBackward true`). Private helper signatures and their proven
bodies add no public declarations. All added imports are proof-only.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoherentIdealPatchingGenericEmbedding | unclaimed | No adaptation: its imported public signature is identical; the attributes are local to the new section. |

| Sheaf.AlgebraicGeometry.CoherentIdealPatchingGenericEmbeddingStalkBijective | unclaimed | No adaptation: the core signature and public imports are unchanged. |

## Status

landed 20261013T022430-L-3220509 2026-10-13 (merge of deliver/U1/Sheaf.AlgebraicGeometry.CoherentIdealPatchingGenericEmbeddingCore)
