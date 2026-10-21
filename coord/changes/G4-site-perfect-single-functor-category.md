# WeilConjectures.IsRationalFiniteProjectiveTerm

## Reason

Restore the quarantined module from the rework assignment dated 2026-10-21.
The old declaration fails at the second localized single functor (archived line 122):
Lean must infer its module category from the finite product of coefficient units,
before elaborating the morphism target that fixes the ambient scalar localization.
A fresh remote compile of the untouched archive reproduces this error in 3.7 s:

```text
SitePerfectComplexBaseline.lean:122:10: error(lean.synthInstanceFailed):
failed to synthesize instance of type class
  Quiver
    (ScalarLocalization (↥(Padic.coefficientExtensionIntegers l E))
      (DerivedCategory (SheafOfModules (completedIntegralCoefficientSheafUnrestricted l E Y)))
      (Padic.coefficientExtensionUniformizer l E))
```

Specify `integralTowerModules l E Y` as the category argument of all four single
functors. This is already the category of M and the ambient localization.
The completed ring presentation in `integralTowerModules` definitionally equals
`completedIntegralCoefficientSheafUnrestricted`; no mathematical data changes.

## Old

```lean
noncomputable def IsRationalFiniteProjectiveTerm (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) (M : integralTowerModules l E Y) : Prop :=
  ∃ m : ℕ,
    ∃ i : (ScalarLocalization.mk ((DerivedCategory.singleFunctor _ 0).obj M) :
        sitePerfectRationalAmbient l E Y) ⟶
      ScalarLocalization.mk ((DerivedCategory.singleFunctor _ 0).obj
        (∏ᶜ fun _ : Fin m ↦
          SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))),
    ∃ p : ScalarLocalization.mk ((DerivedCategory.singleFunctor _ 0).obj
        (∏ᶜ fun _ : Fin m ↦
          SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))) ⟶
      (ScalarLocalization.mk ((DerivedCategory.singleFunctor _ 0).obj M) :
        sitePerfectRationalAmbient l E Y),
    i ≫ p = 𝟙 _
```

## New

```lean
noncomputable def IsRationalFiniteProjectiveTerm (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) (M : integralTowerModules l E Y) : Prop :=
  ∃ m : ℕ,
    ∃ i : (ScalarLocalization.mk
        ((DerivedCategory.singleFunctor (integralTowerModules l E Y) 0).obj M) :
        sitePerfectRationalAmbient l E Y) ⟶
      ScalarLocalization.mk ((DerivedCategory.singleFunctor (integralTowerModules l E Y) 0).obj
        (∏ᶜ fun _ : Fin m ↦
          SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))),
    ∃ p : ScalarLocalization.mk ((DerivedCategory.singleFunctor (integralTowerModules l E Y) 0).obj
        (∏ᶜ fun _ : Fin m ↦
          SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))) ⟶
      (ScalarLocalization.mk
        ((DerivedCategory.singleFunctor (integralTowerModules l E Y) 0).obj M) :
        sitePerfectRationalAmbient l E Y),
    i ≫ p = 𝟙 _
```

## Users

`tools/downstream.py Sheaf.Paper.SitePerfectComplex --allow-missing --uses
IsRationalFiniteProjectiveTerm` lists zero live downstream modules: this item
and its consumers are quarantined. A separate source scan includes the archived
consumers below. Their predicate signatures, ambient categories, and finite-free
retractions are identical. No consumer adaptation is needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Quarantined consumer; unchanged interface, no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Quarantined consumer; unchanged interface, no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Quarantined consumer; unchanged interface, no adaptation. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Quarantined consumer; unchanged interface, no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Quarantined consumer; unchanged interface, no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Quarantined consumer; unchanged interface, no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Quarantined consumer; unchanged interface, no adaptation. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Quarantined consumer; unchanged interface, no adaptation. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Quarantined consumer; unchanged interface, no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Quarantined consumer; unchanged interface, no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Quarantined consumer; unchanged interface, no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Quarantined consumer; unchanged interface, no adaptation. |

The owning DAG attachment `def-weil-site-perfect-complex` remains unchanged,
including its declarations list, statement dependencies, and empty proof plan.
No target type or definition meaning changes, so no target statement re-review
is triggered by this elaboration repair.

The repaired full module compiles remotely in 4.2 s with no errors or warnings.
The archive and repaired source differ only in these four explicit category
arguments and the line wrapping needed to keep 100-character lines.

## Status

landed 20261021T170726-L-2754634 2026-10-21 (merge of deliver/G4/Sheaf.Paper.SitePerfectComplex)
