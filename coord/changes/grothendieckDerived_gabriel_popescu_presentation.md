# grothendieckDerived_gabriel_popescu_presentation

## Reason

The parent proof is decomposed into two admitted component lemmas in dedicated modules.
The abelian component must carry the large-coproduct hypothesis, and the parent keeps its
original public signature and instance lets.

## Old

```lean
theorem grothendieckDerived_gabriel_popescu_presentation
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)] :
    ∃ (S : Type w) (rS : Ring S),
      letI := rS
      ∃ hD : HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S),
      letI := hD
      ∃ (F : ModuleCat.{max w vH} S ⥤ A) (U : A ⥤ ModuleCat.{max w vH} S)
        (adj₀ : F ⊣ U) (addF : F.Additive)
        (limF : PreservesFiniteLimits F) (colimF : PreservesFiniteColimits F),
      letI := addF
      letI := limF
      letI := colimF
      IsIso adj₀.counit ∧
      ∃ (B : Type (max uA vA ((max w vH) + 1))) (cB : Category.{max w vH} B),
      letI := cB
      ∃ (zB : HasZeroObject B) (sB : HasShift B ℤ) (pB : Preadditive B),
      letI := zB
      letI := sB
      letI := pB
      ∃ aB : ∀ n : ℤ, (shiftFunctor B n).Additive,
      letI := aB
      ∃ tB : Pretriangulated B,
      letI := tB
      ∃ (iB : IsTriangulated B) (sumsB : HasCoproducts.{max w vH} B),
      letI := iB
      letI := sumsB
      IsCompactlyGeneratedTriangulated.{max w vH} B ∧
      ∃ (e : B ≌ DerivedCategory (ModuleCat.{max w vH} S))
        (se : e.functor.CommShift ℤ),
      letI := se
      e.functor.IsTriangulated := by
  sorry
```

## New

```lean
theorem grothendieckDerived_gabriel_popescu_presentation
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)] :
    ∃ (S : Type w) (rS : Ring S),
      letI := rS
      ∃ hD : HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S),
      letI := hD
      ∃ (F : ModuleCat.{max w vH} S ⥤ A) (U : A ⥤ ModuleCat.{max w vH} S)
        (adj₀ : F ⊣ U) (addF : F.Additive)
        (limF : PreservesFiniteLimits F) (colimF : PreservesFiniteColimits F),
      letI := addF
      letI := limF
      letI := colimF
      IsIso adj₀.counit ∧
      ∃ (B : Type (max uA vA ((max w vH) + 1))) (cB : Category.{max w vH} B),
      letI := cB
      ∃ (zB : HasZeroObject B) (sB : HasShift B ℤ) (pB : Preadditive B),
      letI := zB
      letI := sB
      letI := pB
      ∃ aB : ∀ n : ℤ, (shiftFunctor B n).Additive,
      letI := aB
      ∃ tB : Pretriangulated B,
      letI := tB
      ∃ (iB : IsTriangulated B) (sumsB : HasCoproducts.{max w vH} B),
      letI := iB
      letI := sumsB
      IsCompactlyGeneratedTriangulated.{max w vH} B ∧
      ∃ (e : B ≌ DerivedCategory (ModuleCat.{max w vH} S))
        (se : e.functor.CommShift ℤ),
      letI := se
      e.functor.IsTriangulated := by
  have hcore :
      ∃ (S : Type w) (rS : Ring S),
        letI := rS
        ∃ hD : HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S),
        letI := hD
        ∃ (F : ModuleCat.{max w vH} S ⥤ A) (U : A ⥤ ModuleCat.{max w vH} S)
          (adj₀ : F ⊣ U) (addF : F.Additive)
          (limF : PreservesFiniteLimits F) (colimF : PreservesFiniteColimits F),
        let _ := addF
        let _ := limF
        let _ := colimF
        IsIso adj₀.counit := by
    exact gabriel_popescu_abelian_core (A := A)
  obtain ⟨S, rS, hD, F, U, adj₀, addF, limF, colimF, hc⟩ := hcore
  letI := rS
  letI := hD
  letI := addF
  letI := limF
  letI := colimF
  refine ⟨S, rS, hD, F, U, adj₀, addF, limF, colimF, hc, ?_⟩
  exact compact_derived_source_core (A := A) (S := S)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.GrothendieckDerivedCompactLocalizationModel | unclaimed | Imports the parent target; its statement is unchanged. |
| all other downstream importers | unclaimed | Existing statements are unchanged. |

## Status

landed 20261013T222404-L-1223076 2026-10-13 (merge of deliver/F3/Sheaf.CategoryTheory.GrothendieckDerivedGabrielPopescuPresentation)
