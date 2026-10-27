# trfPointSectionsComplex, trfPointSourceTower, trfPointTargetTower and the three endomorphisms

## Reason

The inferred result types of the original raw tower constructions make export of
an application of the proved realization take 42 seconds by itself; the full main
file repeatedly exceeds 60 seconds. Reuse the existing named canonical constructions
instead of inferring the same raw constructions again. Keep the six original public
names in a prerequisite data module, publicly re-exported by the original module.
Use explicit endomorphism result types for the two remaining product constructions.

The construction equivalences are already proved in
`PointTransportConeComparisonDescent`: `reductionTowers_eq_original` and
`pullbackTowers_eq_original` identify the canonical towers with the original raw
composition formulas. `PointTransportCone.sections` is exactly the original section
complex functor. `reductionEnd` is the original one-minus-shift product endomorphism
on that tower. The two other endomorphism bodies retain the original formulas,
with explicit result types. Thus the maps, transitions and two cone coordinates
have the same mathematical meaning. No assumption is added, and the original
realization theorem retains the same mathematical statement; its named-predicate
packaging is recorded separately in `G6-integral-point-transport-realization-statement.md`. This definition/presentation repair
is explicitly submitted for independent review of equivalence and compatibility.

## Old

In `Sheaf.Paper.IntegralPointTransportTowerRealization`:

```lean
/-- Termwise integral sections, with the recorded O_E action.
Source: blueprint clause (3) (blueprint: lem-trf-integral-point-transport-tower-realization). -/
abbrev trfPointSectionsComplex :=
  (pointIntegralSections l E D.k).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The evaluated quotient-induced tower, before any localization.
Source: blueprint clause (3), common K-flat model
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointSourceTower :=
  (Functor.ofOpSequence (X := fun n ↦
    unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n)
    (unrestrictedIntegralTransition l E (Spec (.of D.k)))).flip ⋙
      (Functor.whiskeringRight _ _ _).obj (trfPointSectionsComplex D l E)

/-- The evaluated strict tower Res_n g_n^*(P_n), with its coefficient-induced transitions.
Source: blueprint clause (3), completed pullback model
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointTargetTower :=
  integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom ⋙
    (Functor.whiskeringRight _ _ _).obj (trfPointSectionsComplex D l E)

/-- The specified 1-s on the evaluated source tower.
Source: blueprint clause (3), shifted cone
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointSourceEnd (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((trfPointSourceTower D l E).obj P).obj (op n))
    (integralOperationsTowerStep ((trfPointSourceTower D l E).obj P))

/-- The specified 1-s on the evaluated pullback tower.
Source: blueprint clause (3), shifted cone
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointTargetEnd (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((trfPointTargetTower D l E).obj P).obj (op n))
    (integralOperationsTowerStep ((trfPointTargetTower D l E).obj P))

/-- The same 1-s before applying sections.
Source: blueprint clause (3), sectionwise product computation
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointSheafTargetEnd
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦
      ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P).obj (op n))
    (integralOperationsTowerStep
      ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P))
```

## New

In `Sheaf.Paper.IntegralPointTransportTowerData`:

The following concrete localization alias is also added to keep implicit exported
instance arguments short. It is registered only as a local instance in the item.
It has exactly the body used by `CompletedStalk.moduleQ`; no new localization or
arbitrary witness is chosen.

```lean
/-- The recorded small-Hom localization of the ordinary integral module category.
This named construction keeps instance arguments in exported statements short.
Source: Stacks 05RU, as in `CompletedStalk.moduleQ`
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
@[instance_reducible] def trfPointModuleHasDerivedCategory : HasDerivedCategory.{u + 1}
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _
```

The six original names become:

```lean
/-- Termwise integral sections, with the recorded O_E action.
Source: blueprint clause (3) (blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointSectionsComplex :
    CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ ⥤
      CochainComplex
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ :=
  PointTransportCone.sections D l E

/-- The evaluated quotient-induced tower, before any localization.
Source: blueprint clause (3), common K-flat model
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointSourceTower := PointTransportCone.reductionTowers D l E

/-- The evaluated strict tower Res_n g_n^*(P_n), with its coefficient-induced transitions.
Source: blueprint clause (3), completed pullback model
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointTargetTower := PointTransportCone.pullbackTowers D l E

/-- The specified 1-s on the evaluated source tower.
Source: blueprint clause (3), shifted cone
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointSourceEnd (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  PointTransportCone.reductionEnd D l E P

/-- The specified 1-s on the evaluated pullback tower.
Source: blueprint clause (3), shifted cone
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointTargetEnd (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    End (∏ᶜ fun n ↦ ((trfPointTargetTower D l E).obj P).obj (op n)) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((trfPointTargetTower D l E).obj P).obj (op n))
    (integralOperationsTowerStep ((trfPointTargetTower D l E).obj P))

/-- The same 1-s before applying sections.
Source: blueprint clause (3), sectionwise product computation
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def trfPointSheafTargetEnd
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    End (∏ᶜ fun n ↦
      ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P).obj (op n)) :=
  towerTransitionEndomorphism
    (K := fun n ↦
      ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P).obj (op n))
    (integralOperationsTowerStep
      ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P))
```

The original module retains its original six public imports and adds:

```lean
public import Sheaf.Paper.IntegralPointTransportTowerData
```

The data module publicly imports the original public prerequisites and
`Sheaf.Paper.PointTransportConeComparisonDescent`, which provides the canonical
constructions. It also publicly imports
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`, needed
for the small-Hom localization in the public statement on the canonical module
category. Previously this was accessible only through private proof imports.
The new localization alias is `instance_reducible`, as required for a class
definition, and is registered only locally. No existing global reducibility
attribute or instance is changed. The original section-functor abbreviation becomes
a definition with the same body and an explicit canonical result type; this is
part of the interface repair checked against all direct importers. No source-library file is changed.

## Users

A name search in both source roots found no external direct uses of these six
names. The two consumers below compile unchanged. The published local Frobenius
normalization is also checked unchanged, as requested by reviewer C-8fe81.
Temporary unchanged consumer copies are removed after compatibility checks.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed in the current claim snapshot | Existing import exposes the same six names. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed in the current claim snapshot | Existing import exposes the same six names. |

## Status

landed 20261027T050602-L-240395 2026-10-27 (merge of deliver/G6/Sheaf.Paper.IntegralPointTransportTowerRealization)
