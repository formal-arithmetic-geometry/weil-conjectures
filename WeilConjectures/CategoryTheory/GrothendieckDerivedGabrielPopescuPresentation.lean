/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.CompactlyGenerated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.CompactDerivedSourceCore
import WeilConjectures.CategoryTheory.GabrielPopescuAbelianCore

/-! # A common module presentation for compact generation and exact localization

Source: Stacks Project, Tags 0F5V, 0F5X, and 05NU for the size extension.
-/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits

namespace CategoryTheory


/-- The Gabriel--Popescu abelian presentation and the compact triangulated source use
one and the same module category, linked by a triangulated equivalence.
Source: Stacks Project, Tags 0F5V and 0F5X (first paragraph), with Baer criterion 05NU. -/
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
  let := rS
  let := hD
  let := addF
  let := limF
  let := colimF
  refine ⟨S, rS, hD, F, U, adj₀, addF, limF, colimF, hc, ?_⟩
  exact compact_derived_source_core (A := A) (S := S)

end CategoryTheory
