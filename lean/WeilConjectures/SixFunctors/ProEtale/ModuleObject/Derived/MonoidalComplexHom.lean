/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalComplex

/-!
# The tensor comparison of the pullback of module objects on complexes, naturality

Part of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`, split off so that
each file compiles within the time limit: the comparison
`f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` of complexes (`upperStarTensorComplexHom`), its naturality, and
the naturality square `upperStarTensorCounit_naturality_aux`.
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

/-- The comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` of complexes of module objects, induced
degreewise by the tensorator of the strong monoidal pullback `f^*`. -/
noncomputable def upperStarTensorComplexHom
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ⊗
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B ⟶
      ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj (A ⊗ B) where
  f n := upperStarTensorComplexHomX Λ f A B n
  comm' n n' h := upperStarTensorComplexHom_comm Λ f A B n n' h

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The comparison `upperStarTensorComplexHom` is the inverse of the comparison
`f^* (A ⊗ B) ⟶ f^* A ⊗ f^* B` induced by the comonoidal structure of `f^*`. -/
lemma upperStarTensorComplexHom_eq_inv
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    upperStarTensorComplexHom Λ f A B =
      inv (HomologicalComplex.mapBifunctorComparison (Functor.OplaxMonoidal.δNatTrans (f)^*⟦Λ⟧)
        (.up ℤ) A B) := by
  refine (IsIso.inv_eq_of_inv_hom_id (HomologicalComplex.hom_ext _ _ fun n ↦ ?_)).symm
  exact upperStarTensorComplexHomX_comp_mapBifunctorComparisonX Λ f A B n

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The comparison `upperStarTensorComplexHom` is natural in both complexes. -/
lemma upperStarTensorComplexHom_naturality
    {A A' B B' : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ}
    (φ : A ⟶ A') (ψ : B ⟶ B') :
    (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map φ ⊗ₘ
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) ≫
        upperStarTensorComplexHom Λ f A' B' =
      upperStarTensorComplexHom Λ f A B ≫
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map (φ ⊗ₘ ψ) := by
  rw [upperStarTensorComplexHom_eq_inv, upperStarTensorComplexHom_eq_inv, IsIso.comp_inv_eq,
    Category.assoc, IsIso.eq_inv_comp]
  exact (HomologicalComplex.mapBifunctorComparison_naturality
    (Functor.OplaxMonoidal.δNatTrans (f)^*⟦Λ⟧) (.up ℤ) φ ψ).symm

/-! ### The homotopy category -/

/-- The bifunctor `(A, B) ↦ Qh (f^* (A ⊗ B))` on the homotopy category of complexes of module
objects over `Λ_Y`, of which both sides of the comparison are left derived bifunctors. -/
noncomputable def upperStarTensorTarget :
    HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
        (ComplexShape.up ℤ) ⥤
      HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) :=
  curriedTensor _ ⋙ (whiskeringRight _ _ _).obj
    ((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The naturality square of the components of `upperStarTensorCounit`, on complexes. -/
lemma upperStarTensorCounit_naturality_aux
    {A A' B B' : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ}
    (φ : A ⟶ A') (ψ : B ⟶ B') :
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) ⊗ₘ
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ))) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient _ _).obj
          (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A'))
        ((HomotopyCategory.quotient _ _).obj
          (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B')) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (upperStarTensorComplexHom Λ f A' B')) =
    Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient _ _).obj
          (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A))
        ((HomotopyCategory.quotient _ _).obj
          (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (upperStarTensorComplexHom Λ f A B)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map (φ ⊗ₘ ψ))) := by
  have key : ((HomotopyCategory.quotient _ _).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) ⊗ₘ
      (HomotopyCategory.quotient _ _).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ)) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map φ ⊗ₘ
          ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) := by
    rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def, Functor.map_comp]
    rfl
  rw [Functor.LaxMonoidal.μ_natural_assoc, key, ← DerivedCategory.Qh.map_comp,
    ← Functor.map_comp, upperStarTensorComplexHom_naturality, Functor.map_comp,
    DerivedCategory.Qh.map_comp]

end AlgebraicGeometry.ProEtale.CondensedRing
