# localizedOpen_kFlat_tensor_restriction proof context

## Reason

The delivery checker treats changes to `open` and `attribute` commands as interface
changes. These commands are needed to elaborate the proof through the exact
localized-site equivalence. They introduce no exported instance or notation and
change no existing declaration's signature or definition.

## Old

```lean
open CategoryTheory MonoidalCategory
```

No local registration of a tensor structure for the localized carrier and no local
registration of the additive/finite-limit/finite-colimit composition helpers.

## New

```lean
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] loktr_localizedTensor
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
```

`loktr_localizedTensor` is an instance-reducible private noncomputable definition equal to
`SheafOfModules.monoidalCategory (X.sheaf.over U)`. Its local registration is used
only in private helper types and proofs; the original public statement retains
its explicit monoidal structure arguments. Local attributes do not propagate
through imports. The added namespace opening resolves the names of Mathlib
composition instances and does not add declarations.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictPerfectTensorLocalComparison | unclaimed | Sole direct importer; original theorem signature and public import closure unchanged, local proof context does not propagate; no adaptation. |

No exported declaration or global instance is changed. No consumer adaptation is
necessary and no target statement or definition meaning changes.

## Status

landed 20261013T130348-L-3952210 2026-10-13 (merge of deliver/M2/Sheaf.AlgebraicGeometry.LocalizedOpenKFlatTensorRestriction)
