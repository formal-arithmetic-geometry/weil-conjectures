/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Finite power functors and complexes

Source: Stacks Project, Modules on Sites, Tag 03DB.
(blueprint: lem-pur-finite-power-complex).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {A : Type u} [Category.{v} A]

section
variable [HasFiniteProducts A]

/-- The finite categorical power functor. -/
def finitePowerFunctor (d : ℕ) : A ⥤ A where
  obj M := ∏ᶜ fun _ : Fin d ↦ M
  map f := Limits.Pi.map (fun _ : Fin d ↦ f)
  map_id M := by apply Pi.hom_ext; intro i; simp
  map_comp f g := by apply Pi.hom_ext; intro i; simp

/-- Finite power is the diagonal functor followed by the categorical limit.
Source: Stacks Project, Tag 03DB.
(blueprint: lem-pur-finite-power-complex). -/
def finitePowerFunctorIso (d : ℕ) :
    Functor.const (Discrete (Fin d)) ⋙ lim ≅ finitePowerFunctor (A := A) d :=
  NatIso.ofComponents (fun M ↦ (Pi.isoLimit
    ((Functor.const (Discrete (Fin d))).obj M)).symm) (by
      intro M N f
      apply Pi.hom_ext
      intro i
      simp only [Category.assoc]
      change limMap ((Functor.const (Discrete (Fin d))).map f) ≫
          (Pi.isoLimit ((Functor.const (Discrete (Fin d))).obj N)).inv ≫ Pi.π _ i =
        (Pi.isoLimit ((Functor.const (Discrete (Fin d))).obj M)).inv ≫
          Limits.Pi.map (fun _ : Fin d ↦ f) ≫ Pi.π _ i
      rw [Pi.isoLimit_inv_π, Pi.map_π, ← Category.assoc, Pi.isoLimit_inv_π, limMap_π]
      rfl)

instance (d : ℕ) {I : Type*} [Category* I] [HasLimitsOfShape I A] :
    PreservesLimitsOfShape I (finitePowerFunctor (A := A) d) :=
  preservesLimitsOfShape_of_natIso (finitePowerFunctorIso d)

end

section
variable [Preadditive A] [HasFiniteProducts A]

instance (d : ℕ) : (finitePowerFunctor (A := A) d).Additive where
  map_add := by intros; apply Pi.hom_ext; intro i; simp [finitePowerFunctor]

end

section
variable [Abelian A]

instance (d : ℕ) : PreservesFiniteColimits (finitePowerFunctor (A := A) d) := by
  let : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  let : HasExactLimitsOfShape (Discrete (Fin d)) A :=
    hasExactLimitsOfShape_discrete_finite A
  exact preservesFiniteColimits_of_natIso (finitePowerFunctorIso d)

end

section
variable [Abelian A]

end

end CategoryTheory
