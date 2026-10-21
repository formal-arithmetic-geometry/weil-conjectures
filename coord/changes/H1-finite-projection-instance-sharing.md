# AlgebraicGeometry.Scheme.finiteRingCompactSupportProjection

## Reason

The canonical compactification map's derived tensor and realization arguments formerly
contained separately abstracted copies of large inferred instance proofs. Comparing these
copies in a consumer could exceed the 60-second file compilation limit. The repair names
existing propositional instances and reuses those theorem applications locally in the map
and its proof consumer. No mathematical data are chosen, and no premise or conclusion changes.

The local priorities select the commutative-ring projection for the lifted coefficient ring
and the finite-ring Noetherian instance. The coefficient ring operations are unchanged.
The helper theorems are proofs of already available instances, all by `inferInstance`.
They are registered only locally, so importing modules gain no global instance priorities.
The main proof additionally seals complicated functors locally after their comparison API
has been proved, to prevent accidental unfolding during elaboration. It keeps the concrete
coefficient category explicit in its final argument: a local `let A := ModuleCat (ULift R)`
caused repeated kernel conversions even after elaboration succeeded. Removing that alias
reduced the complete proof's kernel check from a deterministic timeout to under a second;
the whole theorem module compiled in 13.3 seconds in the confirming run. No compile limit
was raised. The shipped source removes all diagnostic options and temporary test files.

## Old

```lean
noncomputable def finiteRingCompactSupportProjection
    (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  (Functor.postcompose₂.obj
    (sfIntrinsicModuleEquivalence Y R).functor.mapDerivedCategory).map
      (((((Functor.whiskeringLeft₂ _).obj
        (sfIntrinsicModuleEquivalence X R).inverse.mapDerivedCategory).obj
          (sfIntrinsicModuleEquivalence Y R).inverse.mapDerivedCategory)).map
            (ProEtale.projectionMapOfCompactification
              (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c))
```

## New

The definition above is retained verbatim. The following proved theorem applications are
used as local instance shortcuts when elaborating it and its proof consumer:

```lean
theorem finiteProjection_groupW {X : Scheme.{u}} :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_groupSheafify {X : Scheme.{u}} :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_moduleSheafify (R : Type u) [CommRing R] {X : Scheme.{u}} :
    HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_sheafGroth (R : Type u) [CommRing R] {X : Scheme.{u}} :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} R))) := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_functorLimits (R : Type u) [CommRing R] [Finite R]
    {X : Scheme.{u}} :
    PreservesFiniteLimits (sfIntrinsicModuleEquivalence X R).functor := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_functorColimits (R : Type u) [CommRing R] [Finite R]
    {X : Scheme.{u}} :
    PreservesFiniteColimits (sfIntrinsicModuleEquivalence X R).functor := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_inverseAdditive (R : Type u) [CommRing R] [Finite R]
    {X : Scheme.{u}} :
    (sfIntrinsicModuleEquivalence X R).inverse.Additive := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_inverseLimits (R : Type u) [CommRing R] [Finite R]
    {X : Scheme.{u}} :
    PreservesFiniteLimits (sfIntrinsicModuleEquivalence X R).inverse := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_inverseColimits (R : Type u) [CommRing R] [Finite R]
    {X : Scheme.{u}} :
    PreservesFiniteColimits (sfIntrinsicModuleEquivalence X R).inverse := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_moduleGroth (R : Type u) [CommRing R] :
    IsGrothendieckAbelian.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_modulePreadditive (R : Type u) [CommRing R] :
    MonoidalPreadditive (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_moduleFlat (R : Type u) [CommRing R] :
    Abelian.HasFunctorialFlatResolution
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_upperFlat (R : Type u) [CommRing R] [Finite R] :
    ProEtale.UpperStarPreservesFlat
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) := inferInstance

attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat finiteProjection_upperFlat
```

The local instance selection preceding these helpers is:

```lean
attribute [local instance 2000] CommRing.toRing
attribute [local instance 2000] isNoetherian_of_finite
```

The old and new canonical map have the same source, target, and component morphisms;
only proof arguments to their construction are shared. The target theorem's signature
is unchanged. No adopted `WeilConjectures` module is edited.

## Users

`python3 tools/downstream.py Sheaf.Paper.FiniteRingCompactSupportProjectionMap
--uses finiteRingCompactSupportProjection` reports the map module itself and the single
consumer below. There are no other Lean importers to adapt.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteRingCompactSupportProjectionMap | unclaimed | Add proved instance shortcuts; retain canonical map definition. |
| Sheaf.Paper.FiniteRingCompactSupportProjection | H1 | Reuse shortcuts locally and prove the existing theorem. |

## Status

landed 20261021T013341-L-2288601 2026-10-21 (merge of deliver/H1/Sheaf.Paper.FiniteRingCompactSupportProjection)
