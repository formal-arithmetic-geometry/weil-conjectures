/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalComplexHom

/-!
# The tensor comparison of the pullback of module objects on the homotopy category

Part of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`, split off so that
each file compiles within the time limit: the transformation
`Qh (f^* A) ⊗ᴸ Qh (f^* B) ⟶ Qh (f^* (A ⊗ B))` (`upperStarTensorCounit`).
-/


set_option Elab.async false

@[expose] public section

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The transformation `Qh (f^* A) ⊗ᴸ Qh (f^* B) ⟶ Qh (f^* (A ⊗ B))` of bifunctors on the
homotopy category of `Mod_{Λ_Y}`: the lax structure of `Qh` followed by `Qh` of the comparison
`upperStarTensorComplexHom`. -/
noncomputable def upperStarTensorCounit :
    (((whiskeringLeft₂ _).obj
        ((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)).obj
        ((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)).obj
        (curriedTensor _) ⟶
      upperStarTensorTarget Λ f where
  app A :=
    { app B := Functor.LaxMonoidal.μ DerivedCategory.Qh
          (((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ)).obj B) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          (upperStarTensorComplexHom Λ f A.as B.as))
      naturality B B' ψ := by
        obtain ⟨A, rfl⟩ := A.quotient_obj_surjective
        obtain ⟨B, rfl⟩ := B.quotient_obj_surjective
        obtain ⟨B', rfl⟩ := B'.quotient_obj_surjective
        obtain ⟨ψ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective ψ
        have h := upperStarTensorCounit_naturality_aux Λ f (𝟙 A) ψ
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
          CategoryTheory.Functor.map_id, MonoidalCategory.id_tensorHom,
          MonoidalCategory.id_tensorHom] at h
        rw [Category.assoc]
        exact h }
  naturality A A' φ := by
    ext B
    obtain ⟨A, rfl⟩ := A.quotient_obj_surjective
    obtain ⟨A', rfl⟩ := A'.quotient_obj_surjective
    obtain ⟨B, rfl⟩ := B.quotient_obj_surjective
    obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective φ
    have h := upperStarTensorCounit_naturality_aux Λ f φ (𝟙 B)
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
          CategoryTheory.Functor.map_id, MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_id] at h
    rw [NatTrans.comp_app, NatTrans.comp_app, Category.assoc]
    exact h

end AlgebraicGeometry.ProEtale.CondensedRing
