/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.ProZero

/-!
# Towers of bounded objects with pro-zero homology

Let `F : ℕᵒᵖ ⥤ D(C)` be a tower in the derived category of an abelian category whose terms all
have homology in a fixed interval `[α, β]`. If for every degree `p` the tower of homology
objects `Hᵖ(F)` is pro-zero, then `F` itself is pro-zero
(`DerivedCategory.isProZero_of_homology`).

The proof is an induction on the length of the interval. A map `X ⟶ Y` with `X ≤ β` whose
composite with `Y ⟶ τ_{≥β} Y` vanishes on `Hᵝ` is zero on `τ_{≥β} Y`
(`DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE`), hence factors through
`τ_{<β} Y`; and the tower `τ_{<β} F` has homology in `[α, β - 1]`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open TStructure (t)

/-- The homology towers `Hᵖ(F)` of a tower `F` in the derived category are pro-zero. -/
def HomologyIsProZero (F : ℕᵒᵖ ⥤ DerivedCategory C) : Prop :=
  ∀ (p : ℤ) (a : ℕ), ∃ (b : ℕ) (h : a ≤ b), (homologyFunctor C p).map (F.map (homOfLE h).op) = 0

lemma isProZero_of_homology_aux (α : ℤ) (k : ℕ) :
    ∀ (F : ℕᵒᵖ ⥤ DerivedCategory C), (∀ m, (F.obj m).IsGE α) →
      (∀ m, (F.obj m).IsLE (α + k - 1)) → HomologyIsProZero F → F.IsProZero := by
  induction k with
  | zero =>
    intro F hGE hLE _ a
    refine ⟨a, le_rfl, ?_⟩
    have := hGE (op a)
    have := hLE (op a)
    exact (t.isZero (F.obj (op a)) (α + (0 : ℕ) - 1) α (by lia)).eq_of_src _ _
  | succ k ih =>
    intro F hGE hLE hF a
    set β : ℤ := α + (k + 1 : ℕ) - 1
    let G : ℕᵒᵖ ⥤ DerivedCategory C := F ⋙ t.truncLT β
    have hG : G.IsProZero := by
      refine ih G (fun m ↦ ?_) (fun m ↦ ?_) (fun p a ↦ ?_)
      · have := hGE m
        dsimp [G]
        infer_instance
      · have : ((t.truncLT β).obj (F.obj m)).IsLE (β - 1) := inferInstance
        exact t.isLE_of_le _ _ _ (by simp [β]; lia)
      · obtain ⟨b, hab, hb⟩ := hF p a
        refine ⟨b, hab, ?_⟩
        by_cases hp : p < β
        · have := isIso_homologyFunctor_map_truncLTι_app (F.obj (op a)) β p hp
          rw [← cancel_mono ((homologyFunctor C p).map ((t.truncLTι β).app (F.obj (op a)))),
            zero_comp, ← Functor.map_comp]
          change (homologyFunctor C p).map ((t.truncLT β).map _ ≫ _) = 0
          rw [(t.truncLTι β).naturality, Functor.map_comp, Functor.id_map, hb, comp_zero]
        · have : ((t.truncLT β).obj (F.obj (op a))).IsLE (β - 1) := inferInstance
          exact (isZero_of_isLE _ (β - 1) p (by lia)).eq_of_tgt _ _
    obtain ⟨a₁, ha₁, h₁⟩ := hG a
    obtain ⟨b, hb, h₂⟩ := hF β a₁
    refine ⟨b, ha₁.trans hb, ?_⟩
    have hLEb := hLE (op b)
    -- `F (b ⟶ a₁)` vanishes on `τ_{≥β}`, hence factors through `τ_{<β} F(a₁)`
    have hπ : F.map (homOfLE hb).op ≫ (t.truncGEπ β).app (F.obj (op a₁)) = 0 := by
      have : (F.obj (op b)).IsLE β := hLEb
      apply (homologyFunctor_map_bijective_of_isLE_of_isGE (X := F.obj (op b))
        (Y := (t.truncGE β).obj (F.obj (op a₁))) β).1
      simp only [Functor.map_comp, h₂, zero_comp, Functor.map_zero]
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (t.triangleLTGE_distinguished β (F.obj (op a₁)))
      (F.map (homOfLE hb).op) hπ
    have hcomp : (homOfLE (ha₁.trans hb)).op = (homOfLE hb).op ≫ (homOfLE ha₁).op := rfl
    rw [hcomp, F.map_comp, hg]
    change g ≫ (t.truncLTι β).app (F.obj (op a₁)) ≫ F.map (homOfLE ha₁).op = 0
    rw [← (t.truncLTι β).naturality]
    change g ≫ G.map (homOfLE ha₁).op ≫ _ = 0
    rw [h₁, zero_comp, comp_zero]

/-- **A tower of bounded objects with pro-zero homology is pro-zero.** If the terms of a tower
`F : ℕᵒᵖ ⥤ D(C)` all have homology in `[α, β]` and the homology towers `Hᵖ(F)` are pro-zero,
then `F` is pro-zero. -/
theorem isProZero_of_homology (F : ℕᵒᵖ ⥤ DerivedCategory C) (α β : ℤ)
    (hGE : ∀ m, (F.obj m).IsGE α) (hLE : ∀ m, (F.obj m).IsLE β) (hF : HomologyIsProZero F) :
    F.IsProZero := by
  by_cases h : α ≤ β + 1
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, β = α + k - 1 := ⟨(β - α + 1).toNat, by lia⟩
    exact isProZero_of_homology_aux α k F hGE (fun m ↦ hk ▸ hLE m) hF
  · intro a
    refine ⟨a, le_rfl, ?_⟩
    have := hGE (op a)
    have := hLE (op a)
    exact (t.isZero (F.obj (op a)) β α (by lia)).eq_of_src _ _

end DerivedCategory
