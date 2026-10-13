# AlgebraicGeometry.openComparisonModuleAbelian and openComparisonOverModuleAbelian

## Reason

The complete comparison proof exceeded the single-file compiler limit when each use
reconstructed Mathlib's abelian structures on module sheaves. Transparent abbreviations
of the existing instances, installed as local instances with priority 2000, reduce the
full compilation to 40.1 seconds. These are caches of existing data, not new mathematical
constructions. No existing declaration's signature, visibility or definition is edited.
The static preflight also notices local attributes and scoped elaboration options;
these have no exported instance attribute or mathematical effect.

## Old

Neither abbreviation existed. The canonical instances were synthesized directly from
Mathlib. The original local instance command remains unchanged:

```lean
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
```

## New

```lean
abbrev openComparisonModuleAbelian (X : RingedSpace.{u}) :
    Abelian (SheafOfModules.{u} (moduleRings X)) := inferInstance

abbrev openComparisonOverModuleAbelian (X : RingedSpace.{u})
    (V : TopologicalSpace.Opens X) :
    Abelian (SheafOfModules.{u} ((moduleRings X).over V)) := inferInstance

attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
```

Each body is exactly Mathlib's existing canonical abelian instance. Being abbreviations,
they are definitionally equal to those instances. Their local instance attributes do
not propagate to importing files. No target meaning changes or statement review is
reopened. The new proof uses private, fully proved helpers and scoped elaboration options.

## Users

A repository text search finds no users of either new name, since both are new. No
original public definition or signature changes, and no downstream adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OpenSectionsCohomologyModel | R3 | Uses local canonical caches; proves the existing comparison theorem. |

## Status

landed 20261013T160712-L-1372097 2026-10-13 (merge of deliver/R3/Sheaf.AlgebraicGeometry.OpenSectionsCohomologyModel)
