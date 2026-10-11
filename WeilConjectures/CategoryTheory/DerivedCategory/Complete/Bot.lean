/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Principal
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic

/-!
# Derived completeness for the zero ideal

Every object of `D(J, R)` is derived complete for the zero ideal `⊥`: the tower of reductions
`K ⊗ᴸ R/⊥ⁿ` is constant equal to `K` from `n = 1` on. This complements
`DerivedCategory.derivedComplete_iff_rightOrthogonal`, which needs a nonzerodivisor generator.

## Main results

- `CategoryTheory.Pretriangulated.IsHomotopyLimit.of_isIso_π_succ`: a cone over a tower whose
  legs are isomorphisms from the index `1` on is a homotopy limit cone.
- `DerivedCategory.derivedComplete_bot`: every object is derived complete for `⊥`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite Pretriangulated

namespace CategoryTheory.Pretriangulated.IsHomotopyLimit

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- A cone over a tower whose legs are isomorphisms from the index `1` on is a homotopy limit
cone: the tower is pro-isomorphic to the constant tower on the cone point. -/
lemma of_isIso_π_succ {F : ℕᵒᵖ ⥤ C} (c : Cone F) [∀ n : ℕ, IsIso (c.π.app (op (n + 1)))]
    [HasProduct fun n : ℕ ↦ F.obj (op n)] [HasProduct fun _ : ℕ ↦ c.pt] :
    IsHomotopyLimit c := by
  let P : Fan fun n : ℕ ↦ F.obj (op n) := Fan.mk _ (Pi.π _)
  have hP : IsLimit P := productIsProduct _
  obtain ⟨Fp, ι, ε, hT⟩ := distinguished_cocone_triangle₁ (𝟙 P.pt - towerShift hP)
  let c₀ : Cone ((Functor.const ℕᵒᵖ).obj c.pt) := { pt := c.pt, π := 𝟙 _ }
  have : ∀ n, IsIso (c₀.π.app n) := fun n ↦ by dsimp [c₀]; infer_instance
  have : HasProduct fun n : ℕ ↦ ((Functor.const ℕᵒᵖ).obj c.pt).obj (op n) :=
    ‹HasProduct fun _ : ℕ ↦ c.pt›
  obtain ⟨PK, hPK, δK, hTK⟩ := IsHomotopyLimit.of_isIso_π c₀
  let m := productTowerMap (PF := PK) hP c.π
  obtain ⟨φ, hφ₁, hφ₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hTK hT m m
    (productTowerMap_comp_sub_towerShift hPK hP c.π).symm
  replace hφ₁ : Fan.IsLimit.lift hPK (fun n ↦ c₀.π.app (op n)) ≫ m = φ ≫ ι := hφ₁
  replace hφ₃ : δK ≫ φ⟦(1 : ℤ)⟧' = m ≫ ε := hφ₃
  have hlift : Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) =
      Fan.IsLimit.lift hPK (fun n ↦ c₀.π.app (op n)) ≫ m :=
    Fan.IsLimit.hom_ext hP _ _ fun n ↦ by simp [m, c₀]
  have : IsIso φ := isIso_of_proIso hPK hP hTK hT c.π
    (fun n ↦ inv (c.π.app (op (n + 1))))
    (fun n ↦ by rw [IsIso.inv_comp_eq, c.w])
    (fun n ↦ by simp)
    φ hφ₁ hφ₃
  refine ⟨_, hP, ε ≫ (inv φ)⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (asIso φ) (Iso.refl _) (Iso.refl _) ?_ (by simp) ?_)⟩
  · change Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) ≫ 𝟙 _ = φ ≫ ι
    rw [comp_id, hlift, hφ₁]
  · change (ε ≫ (inv φ)⟦(1 : ℤ)⟧') ≫ φ⟦(1 : ℤ)⟧' = 𝟙 _ ≫ ε
    rw [assoc, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, comp_id,
      id_comp]

end CategoryTheory.Pretriangulated.IsHomotopyLimit

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]

attribute [-instance] commShift₂CurriedTensor commShiftTensorLeft commShiftTensorRight
  isTriangulated_tensorLeft isTriangulated_tensorRight monoidalPreadditive monoidalLinear

noncomputable local instance (priority := high) :
    MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalCategory

local instance : IsIso (sheafTensorStructure J R).ε := (sheafTensorStructure J R).isIso_ε

/-- The quotient map `R ⟶ R ⧸ ⊥ⁿ⁺¹` is an isomorphism. -/
lemma isIso_quotPowCone_π_bot (n : ℕ) :
    IsIso ((Ideal.quotPowCone (⊥ : Ideal R)).π.app (op (n + 1))) := by
  have h : (⊥ : Ideal R) ^ (n + 1) = ⊥ := by rw [pow_succ, Ideal.mul_bot]
  let e := (Submodule.quotEquivOfEqBot _ h).symm.toModuleIso
  have : (Ideal.quotPowCone (⊥ : Ideal R)).π.app (op (n + 1)) = e.hom := rfl
  rw [this]
  infer_instance

/-- Every object of `D(J, R)` is derived complete for the zero ideal. -/
theorem derivedComplete_bot (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    derivedComplete J ⊥ K := by
  have (n : ℕ) : IsIso ((derivedCompletionCone J ⊥ K).π.app (op (n + 1))) := by
    have := isIso_quotPowCone_π_bot (R := R) n
    change IsIso ((ρ_ K).inv ≫ K ◁ ((sheafTensorStructure J R).ε ≫
      (singleFunctor (Sheaf J (ModuleCat.{u + 1} R)) 0).map
        ((constantSheaf J (ModuleCat.{u + 1} R)).map
          ((Ideal.quotPowCone ⊥).π.app (op (n + 1))))))
    infer_instance
  exact IsHomotopyLimit.of_isIso_π_succ _

end DerivedCategory
