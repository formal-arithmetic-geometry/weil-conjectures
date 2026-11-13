/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
@[expose] public section
universe v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
private theorem power_inclusion {X : Scheme.{v}} {P : X.Modules}
    (ι : P ⟶ SheafOfModules.unit X.ringCatSheaf) (k n : ℕ) (h : n ≤ k) :
    ∃ u : (Scheme.idealSheafPower ι k).1 ⟶ (Scheme.idealSheafPower ι n).1,
      u ≫ (Scheme.idealSheafPower ι n).2 = (Scheme.idealSheafPower ι k).2 := by
  induction k with
  | zero =>
    have hn : n = 0 := Nat.eq_zero_of_le_zero h
    subst n
    exact ⟨𝟙 _, by simp⟩
  | succ k ih =>
    by_cases hn : n = k + 1
    · subst n
      exact ⟨𝟙 _, by simp⟩
    · obtain ⟨u, hu⟩ := ih (Nat.le_of_lt_succ (lt_of_le_of_ne h hn))
      have hs : ∃ t : (Scheme.idealSheafPower ι (k + 1)).1 ⟶
          (Scheme.idealSheafPower ι k).1,
          t ≫ (Scheme.idealSheafPower ι k).2 =
            (Scheme.idealSheafPower ι (k + 1)).2 := by
        cases k with
        | zero => exact ⟨ι, by simp [Scheme.idealSheafPower]⟩
        | succ k =>
          exact ⟨Scheme.idealModuleProductι ι _, rfl⟩
      obtain ⟨t, ht⟩ := hs
      exact ⟨t ≫ u, by rw [Category.assoc, hu, ht]⟩

private theorem product_inclusion {X : Scheme.{v}} {P Q : X.Modules}
    (ι : P ⟶ SheafOfModules.unit X.ringCatSheaf)
    (κ : Q ⟶ SheafOfModules.unit X.ringCatSheaf) (u : P ⟶ Q) (hu : u ≫ κ = ι)
    (F : X.Modules) :
    ∃ t : Scheme.idealModuleProduct ι F ⟶ Scheme.idealModuleProduct κ F,
      t ≫ Scheme.idealModuleProductι κ F = Scheme.idealModuleProductι ι F := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have hs : (u ▷ F) ≫ (κ ▷ F ≫ (λ_ F).hom) = (ι ▷ F ≫ (λ_ F).hom) ≫ 𝟙 F := by
    simp only [Category.comp_id, ← Category.assoc, ← comp_whiskerRight, hu]
  refine ⟨image.map (Arrow.homMk' (u ▷ F) (𝟙 F) hs), ?_⟩
  exact (image.map_ι (Arrow.homMk' (u ▷ F) (𝟙 F) hs)).trans (Category.comp_id _)

/-- Transition maps for ideal powers on any scheme and any module (Stacks, Tag 02OA). -/
theorem cohomology_powers_ideal_transition_maps
    {X : Scheme.{v}} (J : X.IdealSheafData) (F : X.Modules) :
    ∃ i : ∀ (k n : ℕ), n ≤ k →
        (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι k).2 F ⟶
          Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F),
      (∀ (k n : ℕ) (h : n ≤ k),
        i k n h ≫ Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F =
          Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι k).2 F) := by
  classical
  have hex : ∀ (k n : ℕ) (h : n ≤ k),
      ∃ t : Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι k).2 F ⟶
          Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F,
        t ≫ Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F =
          Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι k).2 F := by
    intro k n h
    obtain ⟨u, hu⟩ := power_inclusion J.toModulesι k n h
    exact product_inclusion _ _ u hu F
  exact ⟨fun k n h ↦ (hex k n h).choose, fun k n h ↦ (hex k n h).choose_spec⟩
end AlgebraicGeometry
