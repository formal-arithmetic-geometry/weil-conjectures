# AlgebraicGeometry.tensorCounit_smallColimits

## Reason

Elaboration of the total tensor complexes repeatedly searches for their coproduct
existence proofs through the sheaf and cochain-complex presentations. Cache the existing
small colimits and their specializations locally to the assigned module. The named cache
instances are public declarations, although their instance registrations are local, so
this record documents the addition of those names to the module's interface.

The four new declarations are `AlgebraicGeometry.tensorCounit_smallColimits`,
`AlgebraicGeometry.tensorCounit_colimit`,
`AlgebraicGeometry.tensorCounit_hasMapBifunctor`, and
`AlgebraicGeometry.tensorCounit_cochainHasMapBifunctor`. They reuse
`hasColimitsOfSizeShrink`, `HasColimitsOfSize.has_colimits_of_shape`, and
`HasColimitsOfShape.has_colimit` for the existing Grothendieck category of sheaf modules.
They prove propositions about already available colimits; they introduce no new tensor
structure and no new choice of an arbitrary object from an unproved existence theorem.

All existing signatures and definitions, including `tensorCounit_coordinateEquation`,
are unchanged. Proof irrelevance identifies the cached colimit-existence arguments with
the previously inferred ones. The local registrations are not exported as global
instances. No target meaning changes and no downstream adaptation is required.

## Old

The module had the following local registration and none of the four cache declarations:

```lean
attribute [local instance] SheafOfModules.isGrothendieckAbelian
```

## New

```lean
attribute [local instance] SheafOfModules.isGrothendieckAbelian
attribute [local instance] pullbackDescentModuleTensor moduleSymmetric modulePreadditive
  moduleClosed moduleGrothendieck moduleResolutions moduleDerivedMonoidal pullbackDescentQLax

/-- Cache the small colimits used to elaborate total tensor complexes.
Source: Stacks, Tag 079U (blueprint: lem-pc-tensor-counit-coordinate-equation). -/
local instance tensorCounit_smallColimits (S : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings S.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u, u} _

/-- Use the cached small-colimit structure directly for each diagram.
Source: Stacks, Tag 079U (blueprint: lem-pc-tensor-counit-coordinate-equation). -/
local instance tensorCounit_colimit (S : Scheme.{u}) (J : Type) [Category.{0} J]
    (F : J ⥤ SheafOfModules.{u} (moduleRings S.toRingedSpace)) : HasColimit F :=
  ((tensorCounit_smallColimits S).has_colimits_of_shape J).has_colimit F

/-- Tensor total complexes have their defining coproducts.
Source: Stacks, Tag 079U (blueprint: lem-pc-tensor-counit-coordinate-equation). -/
local instance tensorCounit_hasMapBifunctor (S : Scheme.{u})
    (P G : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ) :
    HomologicalComplex.HasMapBifunctor P G
      (curriedTensor (SheafOfModules.{u} (moduleRings S.toRingedSpace))) (.up ℤ) := by
  intro n
  exact tensorCounit_colimit S _ _

/-- The cochain-complex presentation uses the same total coproducts.
Source: Stacks, Tag 079U (blueprint: lem-pc-tensor-counit-coordinate-equation). -/
local instance tensorCounit_cochainHasMapBifunctor (S : Scheme.{u})
    (P G : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ) :
    CochainComplex.HasMapBifunctor P G
      (curriedTensor (SheafOfModules.{u} (moduleRings S.toRingedSpace))) :=
  tensorCounit_hasMapBifunctor S P G
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.TensorCounitCoordinateEquation | H4 | Local elaboration caches and four new public names; existing signature unchanged. |

No existing library module refers to any of the four new names, since they were absent
from the library. Existing importers, including TensorCounitOneKFlatCoordinates, continue
to use the unchanged coordinate-equation interface. There are no forced adaptations.

## Status

landed 20261013T130348-L-3952067 2026-10-13 (merge of deliver/H4/Sheaf.AlgebraicGeometry.TensorCounitCoordinateEquation)
