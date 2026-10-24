/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

set_option maxHeartbeats 1000000 in
-- `erw` unfolds the tensor product of complexes of module objects to its components.
/-- On complexes, the comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` is compatible with the
composition isomorphism of the pullbacks of module objects. -/
@[reassoc]
lemma upperStarTensorComplexHom_comp
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) ℤ) :
    ((NatTrans.mapHomologicalComplex (upperStarComp Λ f g).hom (ComplexShape.up ℤ)).app A ⊗ₘ
        (NatTrans.mapHomologicalComplex (upperStarComp Λ f g).hom (ComplexShape.up ℤ)).app B) ≫
        upperStarTensorComplexHom Λ f (((g)^*⟦Λ⟧.mapHomologicalComplex _).obj A)
          (((g)^*⟦Λ⟧.mapHomologicalComplex _).obj B) ≫
        ((f)^*⟦Λ⟧.mapHomologicalComplex _).map (upperStarTensorComplexHom Λ g A B) =
      upperStarTensorComplexHom Λ (f ≫ g) A B ≫
        (NatTrans.mapHomologicalComplex (upperStarComp Λ f g).hom _).app (A ⊗ B) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    upperStarTensorComplexHom, upperStarTensorComplexHomX]
  erw [HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorDesc_assoc,
    HomologicalComplex.ι_mapBifunctorDesc_assoc]
  rw [Category.assoc, ← Functor.map_comp]
  erw [HomologicalComplex.ι_mapBifunctorDesc]
  simp only [NatTrans.mapHomologicalComplex_app_f, Category.assoc]
  rw [(upperStarComp Λ f g).hom.naturality, Functor.map_comp]
  have hμ := upperStarComp_hom_app_tensor_μ_assoc Λ f g (A.X p) (B.X q)
    ((f)^*⟦Λ⟧.map ((g)^*⟦Λ⟧.map (HomologicalComplex.ιTensorObj A B p q n h)))
  rw [MonoidalCategory.tensorHom_def_assoc] at hμ
  exact hμ

end AlgebraicGeometry.ProEtale.CondensedRing
