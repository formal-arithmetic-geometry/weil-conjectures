# tensorGradedKernel_locally_ideal

## Reason

The stage-3 static interface check conservatively flags changed top-level commands.
This proof needs scoped tensor-product notation and locally registered monoidal
instances to use the existing tensorator. The old local irreducibility registrations
are restricted to the private kernel-factor helper so the final section calculation
can unfold the underlying algebra module. No global instance or attribute is added,
no public import changes, and every existing declaration keeps its signature and
visibility. The command changes affect elaboration inside this file only. There are
no downstream adaptations and no target needs semantic re-review.

## Old

The original local command block, following the unchanged namespaces and section:

```lean
attribute [local irreducible] tensorGradedAlgebraMap tensorGradedUnit
  commAlgebraSheafModule tensorPullback
```

The file had no scoped TensorProduct opening or local monoidal instance registrations.
Its sole public theorem is `AlgebraicGeometry.Scheme.Modules.tensorGradedKernel_locally_ideal`;
its signature is identical in the new file.

## New

Before the namespace:

```lean
open scoped TensorProduct
```

Inside the existing noncomputable section, for the proved private tensor helpers:

```lean
attribute [local instance] presheafMonoidalCategory presheafSymmetricCategory
  sheafificationMonoidal sheafificationBraided forgetToPresheafOfModulesLaxMonoidal
```

The original irreducibility block is scoped to the proved private kernel-factor helper:

```lean
section KernelFactor
attribute [local irreducible] tensorGradedAlgebraMap tensorGradedUnit
  commAlgebraSheafModule tensorPullback
```

That section ends before the public theorem, restoring the original definitions'
ordinary reducibility there. The private helper has a declaration-local heartbeat
budget of 1000000 for adjunction and ideal-multiplication elaboration; the single-file
60-second limit is unchanged. All additions are proved private theorems.

## Users

`tools/downstream.py` finds 186 transitive importers and two textual declaration users
(including the defining module). Because the public signature, definitions, public
imports and global registrations are unchanged, every transitive importer's statements
retain their meaning. The only downstream declaration user is the square-zero lemma.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.TensorGradedKernelLocalIdeal | Q3 | Own module; proof-local elaboration commands and proved private helpers. |
| Sheaf.AlgebraicGeometry.TensorGradedKernelSquareZero | unclaimed | Calls the identical public theorem; no adaptation needed. |

## Status

landed 20261014T061028-L-2466529 2026-10-14 (merge of deliver/Q3/Sheaf.AlgebraicGeometry.TensorGradedKernelLocalIdeal)
