# AlgebraicGeometry.ProEtale.DifferenceCoordinateSection.normalizedE

## Reason

The independent first and second input calculations need the existing normalized
comparison, while the assembly theorem imports those calculations. Move its declaration
verbatim to `Sheaf.Paper.DifferenceFirstInputRestriction` and publicly reexport that module
from the original module. This removes an import cycle without changing the construction,
its type, its name, its visibility or any equation. No mathematical definition changes.
The two input statements are separate strict parts of the original conjunction.

## Old

In `Sheaf.Paper.DifferenceCoordinateSectionIdentifications`:

```lean
def normalizedE (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y B : Scheme.{u}} (v : X ⟶ Y) (h : Y ⟶ B) (h' : X ⟶ B)
    [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated h'] [LocallyOfFiniteType h'] [QuasiCompact h']
    [HasCompactification h] [HasCompactification h']
    (hv : h' = v ≫ h) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] :
    Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) h' ≅
      (pull P v).obj (Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) h) :=
  letI : B.Over (Spec (.of P.field.k)) := ⟨aB⟩
  letI : Y.Over (Spec (.of P.field.k)) := ⟨h ≫ aB⟩
  letI : X.Over (Spec (.of P.field.k)) := ⟨h' ≫ aB⟩
  letI : h.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : h'.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : v.IsOver (Spec (.of P.field.k)) :=
    ⟨(Category.assoc v h aB).symm.trans (congrArg (fun t ↦ t ≫ aB) hv.symm)⟩
  letI : LocallyOfFiniteType (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aB)
  letI : QuasiCompact (B ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aB)
  letI : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (h ≫ aB))
  letI : QuasiCompact (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (h ≫ aB))
  letI : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (h' ≫ aB))
  letI : QuasiCompact (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (h' ≫ aB))
  (FiniteEtaleNormalization.congr P h' (v ≫ h) hv).app
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) B) ≪≫
    sourceEtale P v h
```

## New

The identical declaration above is in `Sheaf.Paper.DifferenceFirstInputRestriction`.
The original module publicly imports that module. Its main theorem signature remains verbatim. The separate Statement-projections
record documents a refactor of geometry bindings with the same formulas. Existing public imports are retained.

## Users

`python3 tools/downstream.py Sheaf.Paper.DifferenceCoordinateSectionIdentifications
--uses AlgebraicGeometry.ProEtale.DifferenceCoordinateSection.normalizedE` reports no
downstream importers and only the original module's eight direct occurrences.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | Y7 | Same public comparison through public reexport; proof now assembles two input calculations and the output composition equation. |
| Sheaf.Paper.DifferenceFirstInputRestriction | new, Y7 | Holds the unchanged definition and first input statement. |
| Sheaf.Paper.DifferenceSecondInputRestriction | new, Y7 | Uses the unchanged comparison through the first module. |

No consumer adaptations and no changes to target meanings.

## Status

landed 20261025T203833-L-2861968 2026-10-25 (merge of deliver/Y7/Sheaf.Paper.DifferenceCoordinateSectionIdentifications)
