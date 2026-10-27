# coefficientFiniteQuotientExistence and coefficientFiniteQuotientDerivedExistence

## Reason

Give both recorded change-of-rings witnesses explicit result types. These are exactly
the previously inferred types, and their right-hand sides stay unchanged. Keeping the
witness definitions locally irreducible then lets the object and counit proofs project
the required properties without re-elaborating the chosen change-of-rings construction.

## Old

```lean
noncomputable def coefficientFiniteQuotientExistence {m n : ℕ} (h : n ≤ m) :=
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (J := Scheme.ProEt.topology W) (coefficientFiniteQuotient l E W h)

noncomputable def coefficientFiniteQuotientDerivedExistence {m n : ℕ} (h : n ≤ m) :=
  (coefficientFiniteQuotientExistence l E W h).choose_spec.choose_spec.choose_spec.choose_spec.2.2
```

## New

```lean
noncomputable def coefficientFiniteQuotientExistence {m n : ℕ} (h : n ≤ m) :
    ∃ (F : normalizedDVRModules l E W m ⥤ normalizedDVRModules l E W n)
      (hobj : ∀ M : normalizedDVRModules l E W m,
        F.obj M = SheafOfModules.changeOfRings (coefficientFiniteQuotient l E W h) M)
      (_ : ∀ {M N : normalizedDVRModules l E W m} (f : M ⟶ N),
        F.map f = eqToHom (hobj M) ≫
          SheafOfModules.changeOfRingsHom (coefficientFiniteQuotient l E W h) M f ≫
            eqToHom (hobj N).symm)
      (_ : F.Additive),
      (∀ {P Q : CochainComplex (normalizedDVRModules l E W m) ℤ} (f : P ⟶ Q),
        CochainComplex.IsKFlatIndependentCoefficients
          (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P →
        CochainComplex.IsKFlatIndependentCoefficients
          (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) Q →
        QuasiIso f → QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f)) ∧
      (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
        (HomotopyCategory.quasiIso (normalizedDVRModules l E W m) (.up ℤ)) ∧
      ∃ (LF : normalizedDVRDerived l E W m ⥤ normalizedDVRDerived l E W n)
        (ε : DerivedCategory.Qh ⋙ LF ⟶
          F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
        LF.IsLeftDerivedFunctor ε
            (HomotopyCategory.quasiIso (normalizedDVRModules l E W m) (.up ℤ)) ∧
          (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
          ∀ P : CochainComplex (normalizedDVRModules l E W m) ℤ,
            CochainComplex.IsKFlatIndependentCoefficients
              (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P →
              IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (J := Scheme.ProEt.topology W) (coefficientFiniteQuotient l E W h)

noncomputable def coefficientFiniteQuotientDerivedExistence {m n : ℕ} (h : n ≤ m) :
    ∃ (LF : normalizedDVRDerived l E W m ⥤ normalizedDVRDerived l E W n)
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (coefficientFiniteQuotientExtension l E W h).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (normalizedDVRModules l E W m) (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex (normalizedDVRModules l E W m) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients
            (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P →
            IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  (coefficientFiniteQuotientExistence l E W h).choose_spec.choose_spec.choose_spec.choose_spec.2.2
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefDerivedSystemEvaluationCalculus | B3 | Result-type annotations; the same functors, counits and universal witnesses are retained. |

`tools/downstream.py Sheaf.Paper.CoefDerivedSystemEvaluationCalculus --uses
coefficientFiniteQuotientExistence coefficientFiniteQuotientDerivedExistence` finds no
textual users of these declarations outside the item. No consumer adaptation is needed.
No target statement changes.

## Status

landed 20261022T145606-L-2021248 2026-10-22 (merge of deliver/B3/Sheaf.Paper.CoefDerivedSystemEvaluationCalculus)
