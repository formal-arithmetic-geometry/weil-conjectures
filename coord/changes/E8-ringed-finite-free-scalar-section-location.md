# CategoryTheory.ringedFiniteFreeScalarSection

## Reason

The normalized tensor-data theorem needs the existing pure scalar-section definition.
Move the unchanged definition to the Data module and publicly import it from the original
module. The original theorem and all its consumers see exactly the same declaration.

## Old

```lean
def ringedFiniteFreeScalarSection
    (E : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) ⥤ SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    (M : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (E.obj M).val.obj U :=
  (eqToHom (h M).symm).val.app U
    ((((PresheafOfModules.sheafificationAdjunction
      (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients J S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf φ M)).app U)
      (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
```

Defined in Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange.

## New

```lean
def ringedFiniteFreeScalarSection
    (E : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) ⥤ SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    (M : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (E.obj M).val.obj U :=
  (eqToHom (h M).symm).val.app U
    ((((PresheafOfModules.sheafificationAdjunction
      (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients J S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf φ M)).app U)
      (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
```

Defined in Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData and publicly reexported.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange | E8 | same definition reexported |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unchanged | same name and definition |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unchanged | same theorem interface |
| Sheaf.Paper.AdicClosedConstructible | unchanged | same theorem interface |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData | E8 new | definition and tensor data |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeHom | E8 new | normalized transpose theorem |

## Status

landed 20261020T051227-L-1601075 2026-10-20 (merge of deliver/E8/Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange)
