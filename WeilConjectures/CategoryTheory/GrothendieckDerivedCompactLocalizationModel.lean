/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.CompactlyGenerated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckDerivedExactLocalization
import WeilConjectures.CategoryTheory.GrothendieckDerivedGabrielPopescuPresentation

/-! # A compactly generated source for derived Gabriel--Popescu localization

Source: Stacks Project, Tags 0F5V and 0F5X, first paragraph.
-/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits

namespace CategoryTheory

/-- A Grothendieck derived category admits an exact localization from a compactly
 generated triangulated category. Source: Stacks Project, Tag 0F5V and the compact
 generation observation in the first paragraph of Tag 0F5X. -/
theorem grothendieckDerived_compact_localization_model
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)] :
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
      ∃ (L : B ⥤ DerivedCategory A) (R : DerivedCategory A ⥤ B)
        (adj : L ⊣ R) (sL : L.CommShift ℤ),
      letI := sL
      L.IsTriangulated ∧ IsIso adj.counit := by
  obtain ⟨S, rS, hD, F, U, adj₀, addF, limF, colimF, hc₀,
    B, cB, zB, sB, pB, aB, tB, iB, sumsB, hB, e, se, he⟩ :=
    grothendieckDerived_gabriel_popescu_presentation.{w, uA, vA, vH} (A := A)
  let := rS
  let := hD
  let := addF
  let := limF
  let := colimF
  let := cB
  let := zB
  let := sB
  let := pB
  let := aB
  let := tB
  let := iB
  let := sumsB
  let := se
  let := he
  let := adj₀.right_adjoint_additive
  obtain ⟨hL, hc⟩ := grothendieckDerived_exact_localization F U adj₀ hc₀
  let RD := U.rightDerivedFunctor
  let adj := adj₀.mapDerivedCategoryRightDerivedAdjunction
  let L := e.functor ⋙ F.mapDerivedCategory
  let R := RD ⋙ e.inverse
  let adjB : L ⊣ R := e.toAdjunction.comp adj
  have hcB : IsIso adjB.counit := by
    let := hc
    have : ∀ X, IsIso (adjB.counit.app X) := by
      intro X
      change IsIso ((e.toAdjunction.comp adj).counit.app X)
      rw [Adjunction.comp_counit_app]
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact ⟨B, cB, zB, sB, pB, aB, tB, iB, sumsB, hB,
    L, R, adjB, inferInstance, inferInstance, hcB⟩

end CategoryTheory
