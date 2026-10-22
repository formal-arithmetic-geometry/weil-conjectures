# AlgebraicGeometry.Scheme.completedRingStrictFiniteExchange

## Reason

The complete proof uses local reducibility attributes, local category-instance
suppression, additional opened namespaces and transparency options. The interface
index conservatively records these commands even though they only elaborate proofs
in this module. All seven existing public declaration signatures, all existing
non-theorem bodies, and all public imports are unchanged. No target meaning changes.
The only new public declaration is the ordinary scalar compatibility theorem in
its own new module, recorded by its new DAG node. It is imported only for the proof.

## Old

The existing module's recorded commands, verbatim:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory Functor.leftAdjoint
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)
open AlgebraicGeometry.ProEtale.StrictTower
```

## New

The delivery module's recorded commands, verbatim:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped ZeroObject
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory Functor.leftAdjoint limit
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)
open AlgebraicGeometry.ProEtale.StrictTower
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [local implicit_reducible] cbcStrictOpen Functor.mapHomologicalComplex catToReflQuiver
attribute [local irreducible] Functor.mapDerivedCategory cbcStrictOpenModule completedTowerModulePullback completedModulePullback
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] cbcStrictOpen Functor.mapHomologicalComplex catToReflQuiver completedReductionCoefficient reductionCoefficientSystem
attribute [local irreducible] Functor.mapDerivedCategory cbcStrictOpenModule completedTowerModulePullback completedModulePullback
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

The namespace openings provide tensor and zero-object notation in private helpers.
Every `attribute [-instance] ... in` applies to its following private declaration.
The reducibility attributes are local; the options control proof elaboration.
Existing definitions have exactly their original bodies. The independent reader
can compare the seven signatures and four non-theorem bodies with the original.

## Users

`python3 -B tools/downstream.py Sheaf.Paper.CompletedRingStrictFiniteExchange
--uses completedRingStrictFiniteExchange cbcFiniteComparisons_existsUnique
cbcSourceFiniteComparison cbcTargetFiniteComparison cbcFiniteInverse cbcFiniteExchange`
finds exactly these two downstream modules. No module held by another group is
adapted in this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | No signature, definition, instance or public import changes; no adaptation required. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | No signature, definition, instance or public import changes; no adaptation required. |

## Status

landed 20261022T025334-L-1284842 2026-10-22 (merge of deliver/M3/Sheaf.Paper.CompletedRingStrictFiniteExchange)
