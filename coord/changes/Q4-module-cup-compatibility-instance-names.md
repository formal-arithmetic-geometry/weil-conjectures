# ModuleCupNaiveDerivedCompatibility local instance names

## Reason

Repair the dedicated return for `Sheaf.Paper.CechCupPullbackCompat` recorded in
`coord/returns/Q4.md`. The non-module axiom/sorry probe rejects the mandatory
cup-product import closure because anonymous local instance names from
`ModuleCupNaiveDerivedCompatibility` collide with anonymous local instances in
`GlobalTensorPullbackMonoidalNormalization`. The reported collision is
`AlgebraicGeometry.Scheme.Modules.instSymmetricCategorySheafOfModulesOpensCarrierCarrierCommRingCatToRingedSpaceModuleRings_1`.

The existing sandbox repair assigns module-specific names to the seven local
instances of `ModuleCupNaiveDerivedCompatibility`. This module is unclaimed
(no matching entry in `coord/claims`). All instance types, values, priorities,
and local visibility stay the same. Mathematical definitions and theorem
signatures are unchanged. No target statement or meaning changes; only the
anonymous auxiliary constant names change. Naming these auxiliaries prevents
collisions when the module-system imports are flattened by the required probe.
The delivered module is reviewed as an unclaimed support-module repair, not as
a signature-preserving forced adaptation to another group's held module.

Validation: a plain import of `Sheaf.Paper.CechCupPullbackCompat` against the
original shared artifacts reproduces exactly the collision above (1.4 seconds).
The same import against the delivered artifacts succeeds (2.2 seconds). Both
new naturality proofs print only the three permitted axioms. The support module
compiles cleanly in 36.5 seconds.

## Old

```lean
local instance : CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))

local instance : MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance : SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf

local instance : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _

local instance : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
local instance : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X
```

## New

```lean
local instance moduleCupCompatibilityCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))

local instance moduleCupCompatibilityMonoidal :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance moduleCupCompatibilitySymmetric :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf

local instance moduleCupCompatibilityColimits :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _

local instance moduleCupCompatibilityPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance moduleCupCompatibilityClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
local instance moduleCupCompatibilityFlatResolution : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X
```

## Users

The preflight identifies the following users of the affected instance types.
No user mentions the old generated names explicitly; every instance body stays
the same. These modules require no adaptation of their mathematical interfaces.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ModuleCupNaiveDerivedCompatibility | unclaimed | Seven local auxiliary instances receive unique names; bodies unchanged. |
| Sheaf.Paper.CechCupPullbackCompat | Q4 | Same instance data and mathematical statements; no edits required. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft | unclaimed | Same instance data and mathematical statements; no edits required. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight | unclaimed | Same instance data and mathematical statements; no edits required. |
| Sheaf.Paper.ModuleCupEqualDerivedMapsClass | XR61367c5e175182a4 | Same instance data and mathematical statements; no edits required. |
| Sheaf.Paper.ModuleCupRealizationEvaluation | unclaimed | Same instance data and mathematical statements; no edits required. |
| Sheaf.Paper.ModuleCupResolutionInvariance | unclaimed | Same instance data and mathematical statements; no edits required. |

## Status

landed 20261014T115943-L-2408458 2026-10-14 (merge of deliver/Q4/Sheaf.Paper.CechCupPullbackCompat)
