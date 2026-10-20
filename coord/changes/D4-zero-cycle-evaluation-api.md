# coefficientHomZeroEvaluation

## Reason

The raw local-section formula forces Lean to expand the unit sheaf and the Hom
product while checking the normalized global-cochain comparison. Express the same
map through the established unit-sections and internal-Hom sections equivalences.
The output remains evaluation of the identical product projection at the identity
object over U, applied to y. The existing `coefficientHomComponent` selects the recorded product projection.
Both formulas are definitionally equal after unfolding
`SheafOfModules.unitHomEquiv` and `SheafOfModules.homObjSectionsEquiv`.

## Old

```lean
noncomputable def coefficientHomZeroEvaluation
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (z : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0)
    (p : ℤ) (U : Cᵒᵖ) (y : (L.X p).val.obj U) :
    (((coefficientHomResolution.{u, c, v} J A).obj M).X p).val.obj U :=
  let a := ((coefficientHomSectionComplex.{u, c, v} J A L M).iCycles 0 z).val.app U
    (1 : A.obj.obj U)
  let f := (coefficientHomComponent.{u, c, v} J A L
    ((coefficientHomResolution.{u, c, v} J A).obj M) 0 p p (add_zero p)).val.app U
      a
  (f.app (op (Over.mk (𝟙 U.unop)))).hom y
```

## New

```lean
noncomputable def coefficientHomZeroEvaluation
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (z : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0)
    (p : ℤ) (U : Cᵒᵖ) (y : (L.X p).val.obj U) :
    (((coefficientHomResolution.{u, c, v} J A).obj M).X p).val.obj U :=
  let N := ((coefficientHomResolution.{u, c, v} J A).obj M).X p
  let h := SheafOfModules.homObj (R := A) (L.X p) N
  let s := (coefficientHomSectionComplex.{u, c, v} J A L M).iCycles 0 z ≫
    coefficientHomComponent.{u, c, v} J A L
      ((coefficientHomResolution.{u, c, v} J A).obj M) 0 p p (add_zero p)
  ((SheafOfModules.homObjSectionsEquiv (R := A) (L.X p) N)
    (h.unitHomEquiv s)).val.app U y
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientHomZeroClass | D4 | Same local evaluation and theorem statement; proof uses the equivalence API. |

`tools/downstream.py Sheaf.Paper.CoefficientHomZeroClass --uses coefficientHomZeroEvaluation`
finds only this module using the definition. No consumer signature changes. The
statement review for targets depending on the definition is reopened for independent
confirmation of this definitional equality. Validation is recorded in report.md.

## Status

landed 20261020T233114-L-894219 2026-10-20 (merge of deliver/D4/Sheaf.Paper.CoefficientHomZeroClass)
