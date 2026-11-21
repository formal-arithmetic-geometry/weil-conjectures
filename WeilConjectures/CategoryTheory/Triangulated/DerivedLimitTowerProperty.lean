/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerTriangle

/-! # Derived-limit property of a tower limit cone
Source: Stacks Project, Derived Categories, Tags 0BK6, 0BK7 and 070M. -/

@[expose] public section
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- A limit cone of a represented K-injective tower has the derived-limit property.
This is the Roos comparison part of `derivedCategory_towerLimit_core`.
Source: Stacks Project, Derived Categories, Tags 0BK6, 0BK7 and 070M. -/
theorem derivedCategory_towerLimit_property
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A]
    (hP : HasCountableProducts (DerivedCategory A)) :
    letI : HasCountableProducts (DerivedCategory A) := hP
    ∀ (_ : EnoughInjectives A)
      (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
      (K : ℕ → DerivedCategory A) (f : ∀ n : ℕ, K (n + 1) ⟶ K n)
      (_e : I.asFunctor ⋙ DerivedCategory.Q ≅ Functor.ofOpSequence f)
      (c : Cone I.asFunctor), IsLimit c →
      IsDerivedLimit f (DerivedCategory.Q.obj c.pt) := by
  intro hI I _ K f e c hc
  let K₀ := fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (Opposite.op n))
  let f₀ := fun n : ℕ ↦ DerivedCategory.Q.map
    (I.asFunctor.map (homOfLE (Nat.le_succ n)).op)
  let p : DerivedCategory.Q.obj c.pt ⟶ ∏ᶜ K₀ :=
    Pi.lift (fun n : ℕ ↦ DerivedCategory.Q.map (c.π.app (Opposite.op n)))
  obtain ⟨δ, h⟩ := derivedCategory_towerLimit_triangle A hP hI I c hc
  let E : ∏ᶜ K₀ ≅ ∏ᶜ K := Pi.mapIso (fun n ↦ e.app (Opposite.op n))
  have he (n : ℕ) :
      (e.app (Opposite.op (n + 1))).hom ≫ f n =
        f₀ n ≫ (e.app (Opposite.op n)).hom := by
    simpa [f₀] using (e.hom.naturality (homOfLE (Nat.le_succ n)).op).symm
  have hE : E.hom ≫ towerTransitionEndomorphism f =
      towerTransitionEndomorphism f₀ ≫ E.hom := by
    exact towerTransitionEndomorphism_natural_backward f₀ f
      (fun n ↦ (e.app (Opposite.op n)).hom) he
  refine ⟨p ≫ E.hom, E.inv ≫ δ, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism f₀) δ)
      (Pretriangulated.Triangle.mk (p ≫ E.hom) (towerTransitionEndomorphism f) (E.inv ≫ δ))
      (Iso.refl _) E E
      (by simp)
      hE.symm
      (by simp))).mp h

end CategoryTheory
