/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.Derived.DerivedMateComparison
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Evaluating a normalized derived extension

Source: Stacks 0FND, 09T5 and 06YT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a av b bv c cv d dv da db dc dd
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace SheafOfModules
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{da} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{db} B]
  {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{dc} C]
  {D : Type d} [Category.{dv} D] [Abelian D] [HasDerivedCategory.{dd} D]
  {R₁ : B ⥤ A} [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  {R₂ : D ⥤ C} [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  {p₁ : CochainComplex A ℤ → Prop} {p₂ : CochainComplex C ℤ → Prop}
  (d₁ : SystemDerivedLeftExtension R₁ p₁) (d₂ : SystemDerivedLeftExtension R₂ p₂)
  (G : A ⥤ C) [G.Additive]
  (H : B ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (GD : DerivedCategory A ⥤ DerivedCategory C)
  (γ : (DerivedCategory.Q (C := A)) ⋙ GD ≅
    G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (τD : R₁.mapDerivedCategory ⋙ GD ⟶
    H.mapDerivedCategory ⋙ R₂.mapDerivedCategory)

variable
    (τ : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hτ : ∀ K : CochainComplex B ℤ,
      τD.app (DerivedCategory.Q.obj K) ≫
          R₂.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
          R₂.mapDerivedCategoryFactors.hom.app
            ((H.mapHomologicalComplex (.up ℤ)).obj K) =
        GD.map (R₁.mapDerivedCategoryFactors.hom.app K) ≫
          γ.hom.app ((R₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((τ.mapHomologicalComplex (.up ℤ)).app K))
    (ι : G ⋙ d₂.ordinary ≅ d₁.ordinary ⋙ H)
    (hι : ∀ P, d₂.ordinaryAdj.homEquiv _ _ (ι.hom.app P) =
      G.map (d₁.ordinaryAdj.unit.app P) ≫ τ.app (d₁.ordinary.obj P))

end SheafOfModules
