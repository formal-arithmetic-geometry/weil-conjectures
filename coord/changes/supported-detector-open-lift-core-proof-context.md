# AlgebraicGeometry.exists_supported_detector_open_lift_core

## Reason

The proof constructs a zero object and uses exact derived functors. Its elaboration
needs the ZeroObject scoped notation and the existing additive/composition instances.
The interface scanner conservatively treats added commands as interface changes.
All existing declaration signatures, universes, visibility, definitions and public
imports remain identical. No existing user requires adaptation.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
```

The original theorem had no declaration-scoped unused-variable linter option.

## New

```lean
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option linter.unusedVariables false in
```

The linter option applies only to the following existing theorem and silences the
unused existential binder `adj`, whose original name and type remain identical.
The attributes are local and serve only proof elaboration; the scope opening supplies
notation. No new instance declaration or public theorem signature is introduced by
these commands.

## Users

`tools/stage3_delivery.py` downstream-user scanning returned no textual users for
its command-change marker. The sole direct importer is listed for completeness.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLift | unclaimed | Existing imported theorem signature unchanged; no source edit required. |

## Status

landed 20261012T194103-L-452503 2026-10-12 (merge of deliver/C2/Sheaf.AlgebraicGeometry.SupportedDetectorOpenLiftCore)
