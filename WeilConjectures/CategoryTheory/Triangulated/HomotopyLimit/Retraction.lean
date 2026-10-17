/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower

/-!
# Towers which are eventually constant up to a retraction

Let `G : ℕᵒᵖ ⥤ C` be a tower in a pretriangulated category with countable products and let `H`
be an object. Suppose given morphisms of towers `β : G ⟶ const H` and `σ : const H ⟶ G` with
`σ ≫ β = 𝟙` such that every composite of `N` consecutive transition maps of `G` factors as
`Gₙ₊ₙ ──β──▶ H ──σ──▶ Gₙ`. Then for every homotopy limit cone `c` of `G`, the projection
`c.pt ⟶ G₀ ──β──▶ H` is an isomorphism
(`CategoryTheory.Pretriangulated.IsHomotopyLimit.isIso_π_comp_of_retraction`): the tower `G` is
pro-isomorphic to the constant tower `H`.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits Opposite

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma lift_comp_towerShift_pow {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (op n)}
    (hP : IsLimit P) (c : Cone F) (k : ℕ) :
    Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) ≫ (End.of (towerShift hP) ^ k) =
      Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) := by
  induction k with
  | zero => rw [pow_zero, End.one_def, comp_id]
  | succ k ih => rw [pow_succ, End.mul_def, lift_comp_towerShift_assoc, ih]

lemma towerShift_pow_comp_of_distTriang {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (op n)}
    (hP : IsLimit P) {X : C} {c : X ⟶ P.pt} {δ : P.pt ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk c (𝟙 _ - towerShift hP) δ ∈ distTriang C) (k : ℕ) :
    (End.of (towerShift hP) ^ k) ≫ δ = δ := by
  have h₁ : towerShift hP ≫ δ = δ := by
    have : (𝟙 _ - towerShift hP) ≫ δ = 0 := comp_distTriang_mor_zero₂₃ _ hT
    rw [Preadditive.sub_comp, id_comp, sub_eq_zero] at this
    exact this.symm
  induction k with
  | zero => rw [pow_zero, End.one_def, id_comp]
  | succ k ih => rw [pow_succ', End.mul_def, assoc, h₁, ih]

/-- **Towers which are eventually constant up to a retraction.** Let `β : G ⟶ const H` and
`σ : const H ⟶ G` be morphisms of towers with `σ ≫ β = 𝟙` such that the composite of `N`
consecutive transition maps `Gₙ₊ₙ ⟶ Gₙ` is `β ≫ σ`. Then for every homotopy limit cone `c` of
`G`, the map `c.pt ⟶ G₀ ⟶ H` is an isomorphism. -/
theorem IsHomotopyLimit.isIso_π_comp_of_retraction [HasLimitsOfShape (Discrete ℕ) C]
    {G : ℕᵒᵖ ⥤ C} {H : C} (β : G ⟶ (Functor.const ℕᵒᵖ).obj H)
    (σ : (Functor.const ℕᵒᵖ).obj H ⟶ G) (hσ : σ ≫ β = 𝟙 _) (N : ℕ)
    (hN : ∀ n : ℕ, G.map (homOfLE (Nat.le_add_right n N)).op =
      β.app (op (n + N)) ≫ σ.app (op n))
    {c : Cone G} (hc : IsHomotopyLimit c) (k : ℕ) : IsIso (c.π.app (op k) ≫ β.app (op k)) := by
  obtain ⟨PG, hPG, δG, hTG⟩ := hc
  let d : Cone ((Functor.const ℕᵒᵖ).obj H) := ⟨H, 𝟙 _⟩
  have : ∀ n, IsIso (d.π.app n) := fun n ↦ by dsimp [d]; infer_instance
  obtain ⟨PH, hPH, δH, hTH⟩ := IsHomotopyLimit.of_isIso_π d
  have hσβ (n : ℕ) : σ.app (op n) ≫ β.app (op n) = 𝟙 _ := congr_app hσ (op n)
  let B : PG.pt ⟶ PH.pt := productTowerMap (PF := PG) hPH β
  let Cm : PH.pt ⟶ PG.pt := Fan.IsLimit.lift hPG fun n ↦ PH.proj (n + N) ≫ σ.app (op n)
  have hCm (n : ℕ) : Cm ≫ PG.proj n = PH.proj (n + N) ≫ σ.app (op n) := Fan.IsLimit.fac hPG _ n
  have hBC : B ≫ Cm = End.of (towerShift hPG) ^ N :=
    Fan.IsLimit.hom_ext hPG _ _ fun n ↦ by
      rw [assoc, hCm, towerShift_pow_proj, hN]
      simp only [B, productTowerMap_proj_assoc]
  have hCB : Cm ≫ B = End.of (towerShift hPH) ^ N :=
    Fan.IsLimit.hom_ext hPH _ _ fun n ↦ by
      rw [assoc, productTowerMap_proj, reassoc_of% hCm, hσβ, towerShift_pow_proj]
      simp
  have hcommB : (𝟙 _ - towerShift hPG) ≫ B = B ≫ (𝟙 _ - towerShift hPH) :=
    (productTowerMap_comp_sub_towerShift hPG hPH β).symm
  have hcommC : (𝟙 _ - towerShift hPH) ≫ Cm = Cm ≫ (𝟙 _ - towerShift hPG) := by
    refine Fan.IsLimit.hom_ext hPG _ _ fun n ↦ ?_
    have hnat : σ.app (op (n + 1)) ≫ G.map (homOfLE n.le_succ).op = σ.app (op n) := by
      rw [← σ.naturality]
      exact id_comp _
    rw [Preadditive.sub_comp, Preadditive.sub_comp, id_comp, assoc, hCm, towerShift_proj_assoc,
      Preadditive.comp_sub, comp_id, Preadditive.comp_sub, assoc, towerShift_proj,
      reassoc_of% hCm, hnat, hCm, Nat.add_right_comm]
    simp
  obtain ⟨u, hu₁, hu₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hTG hTH B B hcommB
  obtain ⟨v, hv₁, hv₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hTH hTG Cm Cm hcommC
  let φ : Triangle.mk _ (𝟙 _ - towerShift hPG) δG ⟶ Triangle.mk _ (𝟙 _ - towerShift hPH) δH :=
    { hom₁ := u, hom₂ := B, hom₃ := B, comm₁ := hu₁, comm₂ := hcommB, comm₃ := hu₃ }
  let φ' : Triangle.mk _ (𝟙 _ - towerShift hPH) δH ⟶ Triangle.mk _ (𝟙 _ - towerShift hPG) δG :=
    { hom₁ := v, hom₂ := Cm, hom₃ := Cm, comm₁ := hv₁, comm₂ := hcommC, comm₃ := hv₃ }
  have hu : IsIso u := isIso_hom₁_of_comp hTG hTH φ φ'
    (by change _ ≫ B ≫ Cm = _; rw [hBC, lift_comp_towerShift_pow])
    (by change B ≫ Cm ≫ δG = δG; rw [reassoc_of% hBC, towerShift_pow_comp_of_distTriang _ hTG])
    (by change _ ≫ Cm ≫ B = _; rw [hCB, lift_comp_towerShift_pow])
    (by change Cm ≫ B ≫ δH = δH; rw [reassoc_of% hCB, towerShift_pow_comp_of_distTriang _ hTH])
  have hk : c.π.app (op k) ≫ β.app (op k) = u := by
    have := hu₁ =≫ PH.proj k
    simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_mor₁, assoc, Fan.IsLimit.fac,
      B, productTowerMap_proj, Fan.IsLimit.fac_assoc] at this
    simpa [d] using this
  rw [hk]
  exact hu

end CategoryTheory.Pretriangulated
