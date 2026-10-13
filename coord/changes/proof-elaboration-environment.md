# ModuleFinitePresentationAffineReplacement proof elaboration environment

## Reason

The complete proof needs category-theoretic limit names and sheaf-module presentation
names in scope. Three fully proved private helpers cache sheafification and local
bijectivity on iterated slice sites and are registered only locally. The static preflight
classifies changed open/attribute commands as an environment change and requires this
record. These commands do not change the signature or meaning of any public declaration.
The existing theorem is proved without new holes; its public imports are unchanged.

## Old

```lean
open CategoryTheory TopologicalSpace
```

There were no local slice-helper registrations.

## New

```lean
open CategoryTheory CategoryTheory.Limits TopologicalSpace SheafOfModules
```

Inside `AlgebraicGeometry.Scheme.Modules`, the new private, fully proved helper theorems
are registered for this module's proofs with these exact commands:

```lean
attribute [local instance] sliceSheafify
attribute [local instance] sliceWeakSheafify
attribute [local instance] sliceLocallyBijective
```

Every existing signature and visibility is preserved. There are no new global instances,
changed definitions, or added public declarations. This is a record of proof elaboration
commands, not a statement or definition change. Importers require no forced adaptation.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ModuleFinitePresentationAffineReplacement | S3 | Local proof elaboration only; its public theorem signature is unchanged. |

## Status

landed 20261013T124316-L-3777996 2026-10-13 (merge of deliver/S3/Sheaf.AlgebraicGeometry.ModuleFinitePresentationAffineReplacement)
