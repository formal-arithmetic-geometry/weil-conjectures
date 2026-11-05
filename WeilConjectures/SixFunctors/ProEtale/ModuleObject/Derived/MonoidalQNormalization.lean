/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CounitFac

/-!
# The tensor comparison of the derived pullback on images of complexes

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. On the images
`Q P`, `Q T` of complexes of module objects over `Λ_Y`, the tensor comparison
`m : Lf^* (Q P ⊗ᴸ Q T) ⟶ Lf^* (Q P) ⊗ᴸ Lf^* (Q T)` of the derived pullback
(`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor`) is the localization of
the comparison `f^* (P ⊗ T) ⟶ f^* P ⊗ f^* T` of complexes induced by the comonoidal structure of
`f^*`, through the identification `Lf^* ≅ D(f^*)` of the derived pullback of the exact functor
`f^*` with its levelwise extension and the lax monoidal structure of `Q`
(`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor_app_app_Q_obj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The lax structure of `Q`, precomposed with `quotientCompQhIso` in both variables, is the lax
structure of `Qh` followed by `quotientCompQhIso`. -/
private lemma quotientCompQhIso_whisker_μ_Q {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [DerivedCategory.Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (.up ℤ))]
    (P T : CochainComplex C ℤ) :
    (DerivedCategory.quotientCompQhIso C).hom.app P ▷ _ ≫
      _ ◁ (DerivedCategory.quotientCompQhIso C).hom.app T ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q P T =
    Functor.LaxMonoidal.μ DerivedCategory.Qh ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj T) ≫
      DerivedCategory.Qh.map (Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ)) P T) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app (P ⊗ T) := by
  have h : Functor.LaxMonoidal.μ DerivedCategory.Q P T =
      ((DerivedCategory.quotientCompQhIso C).inv.app P ⊗ₘ
        (DerivedCategory.quotientCompQhIso C).inv.app T) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj T) ≫
        DerivedCategory.Qh.map (Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ)) P T)) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app (P ⊗ T) := rfl
  rw [← MonoidalCategory.tensorHom_def_assoc, h, Category.assoc,
    tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app, id_tensorHom_id,
    Category.id_comp]

/-- Variant of `quotientCompQhIso_whisker_μ_Q` with morphisms composed in front of
`quotientCompQhIso` in both variables. -/
private lemma comp_quotientCompQhIso_whisker_μ_Q {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [DerivedCategory.Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (.up ℤ))]
    {U V : DerivedCategory C} {P T : CochainComplex C ℤ}
    (a : U ⟶ (HomotopyCategory.quotient C (.up ℤ) ⋙ DerivedCategory.Qh).obj P)
    (b : V ⟶ (HomotopyCategory.quotient C (.up ℤ) ⋙ DerivedCategory.Qh).obj T) :
    (a ≫ (DerivedCategory.quotientCompQhIso C).hom.app P) ▷ V ≫
      _ ◁ (b ≫ (DerivedCategory.quotientCompQhIso C).hom.app T) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q P T =
    a ▷ V ≫ _ ◁ b ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj T) ≫
      DerivedCategory.Qh.map (Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ)) P T) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app (P ⊗ T) := by
  rw [comp_whiskerRight_assoc, MonoidalCategory.whiskerLeft_comp_assoc, ← whisker_exchange_assoc,
    quotientCompQhIso_whisker_μ_Q]

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- `Lf^* ≅ D(f^*)` followed by the factorization of `D(f^*)` through `Q`, on the image of a
complex, is the counit of `Lf^*` up to `quotientCompQhIso`. -/
@[reassoc]
private lemma leftDerivedFunctor_map_quotientCompQhIso_comp_factors
    (Z : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    (f)^*⟦Λ⟧.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app Z) ≫
      (f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory.hom.app _ ≫
      (f)^*⟦Λ⟧.mapDerivedCategoryFactors.hom.app Z =
    (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj Z) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app
        (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj Z) := by
  rw [(f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
  exact (f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory_hom_app_quotient_obj Z

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- Naturality of the comparison `m` of `Lf^*` along `quotientCompQhIso` in both variables. -/
private lemma leftDerivedUpperStarTensor_naturality_quotientCompQhIso
    (P T : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    {W : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (g : _ ⟶ W) :
    (f)^*⟦Λ⟧.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app P ▷
        (HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh).obj T) ≫
      (f)^*⟦Λ⟧.leftDerivedFunctor.map (DerivedCategory.Q.obj P ◁
        (DerivedCategory.quotientCompQhIso _).hom.app T) ≫
      ((leftDerivedUpperStarTensor Λ f).app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj T) ≫ g =
    ((leftDerivedUpperStarTensor Λ f).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj T)) ≫
      (f)^*⟦Λ⟧.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app P) ▷
        (f)^*⟦Λ⟧.leftDerivedFunctor.obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj T)) ≫
      (f)^*⟦Λ⟧.leftDerivedFunctor.obj (DerivedCategory.Q.obj P) ◁
        (f)^*⟦Λ⟧.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app T) ≫ g := by
  have h₁ : (f)^*⟦Λ⟧.leftDerivedFunctor.map (DerivedCategory.Q.obj P ◁
        (DerivedCategory.quotientCompQhIso _).hom.app T) ≫
      ((leftDerivedUpperStarTensor Λ f).app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj T) =
      ((leftDerivedUpperStarTensor Λ f).app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj T)) ≫
      (f)^*⟦Λ⟧.leftDerivedFunctor.obj (DerivedCategory.Q.obj P) ◁
        (f)^*⟦Λ⟧.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app T) :=
    ((leftDerivedUpperStarTensor Λ f).app (DerivedCategory.Q.obj P)).naturality _
  have h₂ : (f)^*⟦Λ⟧.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app P ▷
        (HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh).obj T) ≫
      ((leftDerivedUpperStarTensor Λ f).app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj T)) =
      ((leftDerivedUpperStarTensor Λ f).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj T)) ≫
      (f)^*⟦Λ⟧.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app P) ▷
        (f)^*⟦Λ⟧.leftDerivedFunctor.obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj T)) :=
    NatTrans.congr_app ((leftDerivedUpperStarTensor Λ f).naturality _) _
  simp only [← Category.assoc]
  rw [Category.assoc ((f)^*⟦Λ⟧.leftDerivedFunctor.map _), h₁, ← Category.assoc, h₂]

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The last step of `leftDerivedUpperStarTensor_app_app_Q_obj`: the counit of `Lf^*` on the
lax structure of the quotient functor (an identity), compared with the comparison morphism
of complexes induced by the comonoidal structure of `f^*`. -/
private lemma leftDerivedFunctorCounit_tensor_quotient
    (P T : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P ⊗
          (HomotopyCategory.quotient _ (.up ℤ)).obj T) ≫
      DerivedCategory.Qh.map (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
        (f)^*⟦Λ⟧).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj T)) ≫
      DerivedCategory.Qh.map (Functor.LaxMonoidal.μ (HomotopyCategory.quotient _ (.up ℤ))
        (((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj P)
        (((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj T)) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app
        (((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj P ⊗
          ((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj T) =
    (f)^*⟦Λ⟧.leftDerivedFunctor.map (DerivedCategory.Qh.map
        (Functor.LaxMonoidal.μ (HomotopyCategory.quotient _ (.up ℤ)) P T)) ≫
      (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj (P ⊗ T)) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app
        (((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj (P ⊗ T)) ≫
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorComparison
        (Functor.OplaxMonoidal.δNatTrans (f)^*⟦Λ⟧) (.up ℤ) P T) := by
  have hq (S : Scheme.{u}) (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) ℤ) :
      Functor.LaxMonoidal.μ (HomotopyCategory.quotient _ (.up ℤ)) A B = 𝟙 _ := rfl
  rw [hq, hq, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp, Category.id_comp, ← NatTrans.naturality]
  rfl

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- **The tensor comparison of `Lf^*` on images of complexes.** For complexes `P`, `T` of module
objects over `Λ_Y`, the comparison `Lf^* (Q P ⊗ᴸ Q T) ⟶ Lf^* (Q P) ⊗ᴸ Lf^* (Q T)`, followed by the
identifications `Lf^* (Q P) ≅ D(f^*) (Q P) ≅ Q (f^* P)` and the lax structure of `Q`, is the
image under `Lf^*` of the lax structure `Q P ⊗ᴸ Q T ⟶ Q (P ⊗ T)` followed by the same
identification and the localization of the comparison `f^* (P ⊗ T) ⟶ f^* P ⊗ f^* T` induced by
the comonoidal structure of `f^*`. -/
lemma leftDerivedUpperStarTensor_app_app_Q_obj
    (P T : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    ((leftDerivedUpperStarTensor Λ f).app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj T) ≫
      ((f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory.hom.app _ ≫
          (f)^*⟦Λ⟧.mapDerivedCategoryFactors.hom.app P) ▷ _ ≫
      _ ◁ ((f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory.hom.app _ ≫
          (f)^*⟦Λ⟧.mapDerivedCategoryFactors.hom.app T) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q (((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj P)
        (((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj T) =
    (f)^*⟦Λ⟧.leftDerivedFunctor.map (Functor.LaxMonoidal.μ DerivedCategory.Q P T) ≫
      (f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory.hom.app _ ≫
      (f)^*⟦Λ⟧.mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorComparison
        (Functor.OplaxMonoidal.δNatTrans (f)^*⟦Λ⟧) (.up ℤ) P T) := by
  rw [← cancel_epi ((f)^*⟦Λ⟧.leftDerivedFunctor.map
    ((DerivedCategory.quotientCompQhIso _).hom.app P ⊗ₘ
      (DerivedCategory.quotientCompQhIso _).hom.app T))]
  -- the right hand side
  rw [← Functor.map_comp_assoc _ (_ ⊗ₘ _) (Functor.LaxMonoidal.μ DerivedCategory.Q P T),
    MonoidalCategory.tensorHom_def_assoc _ _ (Functor.LaxMonoidal.μ DerivedCategory.Q P T),
    quotientCompQhIso_whisker_μ_Q, Functor.map_comp_assoc, Functor.map_comp_assoc]
  rw [leftDerivedFunctor_map_quotientCompQhIso_comp_factors_assoc]
  -- the left hand side
  rw [MonoidalCategory.tensorHom_def ((DerivedCategory.quotientCompQhIso _).hom.app P)
      ((DerivedCategory.quotientCompQhIso _).hom.app T), Functor.map_comp, Category.assoc,
    leftDerivedUpperStarTensor_naturality_quotientCompQhIso, whisker_exchange_assoc,
    ← comp_whiskerRight_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    leftDerivedFunctor_map_quotientCompQhIso_comp_factors,
    leftDerivedFunctor_map_quotientCompQhIso_comp_factors]
  erw [comp_quotientCompQhIso_whisker_μ_Q]
  erw [reassoc_of% (leftDerivedUpperStarTensor_app_app_fac Λ f
    ((HomotopyCategory.quotient _ _).obj P) ((HomotopyCategory.quotient _ _).obj T))]
  exact congrArg ((f)^*⟦Λ⟧.leftDerivedFunctor.map
    (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _) ≫ ·)
    (leftDerivedFunctorCounit_tensor_quotient Λ f P T)

end AlgebraicGeometry.ProEtale.CondensedRing
