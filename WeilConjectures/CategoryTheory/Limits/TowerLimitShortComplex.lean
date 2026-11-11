/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# The short complex `lim F ⟶ ∏ Fₙ ⟶ ∏ Fₙ` of a tower

For a tower `F : ℕᵒᵖ ⥤ C` we form the short complex whose first map is the tuple of limit
projections and whose second map is the transition endomorphism `1 - T` of the product.
It is functorial in the tower, and short exact as soon as `1 - T` is an epimorphism.
-/

@[expose] public section

open CategoryTheory Limits Opposite Category

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] [HasCountableProducts C]

/-- The short complex `lim F ⟶ ∏ₙ Fₙ ⟶ ∏ₙ Fₙ` of a tower `F`, whose first map is the tuple
of limit projections and whose second map is the transition endomorphism `1 - T`. -/
noncomputable def towerLimitShortComplex (F : ℕᵒᵖ ⥤ C) [HasLimit F] : ShortComplex C :=
  ShortComplex.mk (Pi.lift fun n : ℕ ↦ limit.π F (op n))
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ F.obj (op n))
      fun n ↦ F.map (homOfLE (Nat.le_succ n)).op) (by
    apply Pi.hom_ext
    intro n
    simp [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub])

/-- The morphism of short complexes `towerLimitShortComplex F ⟶ towerLimitShortComplex G`
induced by a morphism of towers. -/
noncomputable def towerLimitShortComplexMap {F G : ℕᵒᵖ ⥤ C} [HasLimit F] [HasLimit G]
    (f : F ⟶ G) : towerLimitShortComplex F ⟶ towerLimitShortComplex G where
  τ₁ := limMap f
  τ₂ := Limits.Pi.map fun n : ℕ ↦ f.app (op n)
  τ₃ := Limits.Pi.map fun n : ℕ ↦ f.app (op n)
  comm₁₂ := by
    apply Pi.hom_ext
    intro n
    simp [towerLimitShortComplex]
  comm₂₃ := towerTransitionEndomorphism_natural_backward _ _ _
    fun n ↦ (f.naturality (homOfLE (Nat.le_succ n)).op).symm

/-- The first map of `towerLimitShortComplex F` is a kernel of `1 - T`. -/
noncomputable def towerLimitShortComplex.isLimit (F : ℕᵒᵖ ⥤ C) [HasLimit F] :
    IsLimit (KernelFork.ofι (towerLimitShortComplex F).f (towerLimitShortComplex F).zero) :=
  have h : Fan.IsLimit.lift (productIsProduct (fun n : ℕ ↦ F.obj (op n)))
      (fun n ↦ (limit.cone F).π.app (op n)) = (towerLimitShortComplex F).f :=
    Pi.hom_ext _ _ fun n ↦ by
      simpa [towerLimitShortComplex] using Fan.IsLimit.fac (productIsProduct _) _ n
  IsLimit.ofIsoLimit (Fan.IsLimit.isLimitKernelForkOneSub (productIsProduct _)
    (towerProductShift _) (fun n ↦ Pi.lift_comp_π _ n) (limit.isLimit F))
    (Fork.ext (Iso.refl _) (by simpa using h.symm))

/-- If the transition endomorphism `1 - T` of a tower is an epimorphism, then
`0 ⟶ lim F ⟶ ∏ₙ Fₙ ⟶ ∏ₙ Fₙ ⟶ 0` is short exact. -/
lemma towerLimitShortComplex_shortExact {C : Type*} [Category C] [Abelian C]
    [HasCountableProducts C] (F : ℕᵒᵖ ⥤ C) [HasLimit F]
    (hF : Epi (towerTransitionEndomorphism (K := fun n : ℕ ↦ F.obj (op n))
      fun n ↦ F.map (homOfLE (Nat.le_succ n)).op)) :
    (towerLimitShortComplex F).ShortExact := by
  have : Mono (towerLimitShortComplex F).f :=
    mono_of_isLimit_fork (towerLimitShortComplex.isLimit F)
  have : Epi (towerLimitShortComplex F).g := hF
  exact { exact := ShortComplex.exact_of_f_is_kernel _ (towerLimitShortComplex.isLimit F) }

end CategoryTheory

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]

/-- An additive functor intertwines the transition endomorphisms `1 - T` of a tower product
and of its image, via the product comparison map. -/
@[reassoc]
lemma map_towerTransitionEndomorphism_comp_piComparison (E : C ⥤ D) [E.Additive] (F : ℕ → C)
    [HasProduct F] [HasProduct (fun n ↦ E.obj (F n))] (t : ∀ n, F (n + 1) ⟶ F n) :
    E.map (towerTransitionEndomorphism t) ≫ piComparison E F =
      piComparison E F ≫ towerTransitionEndomorphism (fun n ↦ E.map (t n)) := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, piComparison_comp_π, ← E.map_comp]
  simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
    Category.id_comp, Pi.lift_comp_π, E.map_sub, E.map_comp, Preadditive.comp_sub,
    Category.assoc, piComparison_comp_π, piComparison_comp_π_assoc]

omit [Preadditive C] [Preadditive D] in
/-- The product comparison map of a functor is natural in the family. -/
@[reassoc]
lemma map_piMap_comp_piComparison (E : C ⥤ D) {J : Type*} {F F' : J → C} [HasProduct F]
    [HasProduct F'] [HasProduct (fun n ↦ E.obj (F n))] [HasProduct (fun n ↦ E.obj (F' n))]
    (φ : ∀ j, F j ⟶ F' j) :
    E.map (Limits.Pi.map φ) ≫ piComparison E F' =
      piComparison E F ≫ Limits.Pi.map (fun j ↦ E.map (φ j)) := by
  apply Pi.hom_ext
  intro j
  rw [Category.assoc, piComparison_comp_π, ← E.map_comp, Pi.map_π, Category.assoc, Pi.map_π,
    piComparison_comp_π_assoc, E.map_comp]

end CategoryTheory
