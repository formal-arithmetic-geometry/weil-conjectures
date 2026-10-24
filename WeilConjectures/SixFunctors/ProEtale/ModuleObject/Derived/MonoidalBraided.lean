/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.DerivedBraidingAux
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BraidedModule

/-!

# The derived pullback of module objects is braided

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. The tensor
comparison `m_{K,L} : Lf^* (K ⊗ᴸ L) ⟶ Lf^* K ⊗ᴸ Lf^* L` of the derived pullback of module objects
is compatible with the Koszul braidings `DerivedCategory.braidedCategory'` of the derived tensor
products (`ProEtale.CondensedRing.leftDerivedUpperStarTensor_braiding`).

Both sides of the identity are natural transformations between the bifunctors
`(K, L) ↦ Lf^* (K ⊗ᴸ L)` and `(K, L) ↦ Lf^* K ⊗ᴸ Lf^* L`, the latter a left derived bifunctor,
so it suffices to compare them on complexes. There the identity follows from the compatibility
of the underived pullback `f^*` of module objects with the symmetries
(`ProEtale.CondensedRing.laxBraided_upperStar`), extended to complexes with the Koszul sign rule
(`ProEtale.CondensedRing.upperStarTensorComplexHom_braiding`), and from the characterisation of
the braiding of the derived tensor product by its compatibility with the localization
(`DerivedMonoidal.braiding_hom_μ`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option maxHeartbeats 1000000 in
-- `erw` unfolds the tensor product of complexes of module objects to its components.
/-- On complexes, the comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` is compatible with the Koszul
braidings. -/
@[reassoc]
lemma upperStarTensorComplexHom_braiding
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    upperStarTensorComplexHom Λ f A B ≫
        ((f)^*⟦Λ⟧.mapHomologicalComplex _).map (β_ A B).hom =
      (β_ (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj A)
        (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj B)).hom ≫ upperStarTensorComplexHom Λ f B A := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    upperStarTensorComplexHom, upperStarTensorComplexHomX]
  erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
  rw [Category.assoc, ← Functor.map_comp]
  have hβ : HomologicalComplex.ιTensorObj A B p q n h ≫ (β_ A B).hom.f n = _ :=
    CochainComplex.Monoidal.ι_braiding_hom (K := A) (L := B) p q n h
  have hβ' : HomologicalComplex.ιTensorObj (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj A)
      (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj B) p q n h ≫
        (β_ (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj A)
          (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj B)).hom.f n = _ :=
    CochainComplex.Monoidal.ι_braiding_hom (K := ((f)^*⟦Λ⟧.mapHomologicalComplex _).obj A)
      (L := ((f)^*⟦Λ⟧.mapHomologicalComplex _).obj B) p q n h
  rw [hβ]
  erw [reassoc_of% hβ']
  rw [Functor.map_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc,
    Functor.map_comp]
  erw [HomologicalComplex.ι_mapBifunctorDesc]
  rw [LaxBraided.braided_assoc]
  rfl


/-- The inverse form of `upperStarTensorComplexHom_braiding`. -/
@[reassoc]
lemma braiding_inv_upperStarTensorComplexHom
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    (β_ (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj A)
        (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj B)).inv ≫ upperStarTensorComplexHom Λ f A B =
      upperStarTensorComplexHom Λ f B A ≫
        ((f)^*⟦Λ⟧.mapHomologicalComplex _).map (β_ A B).inv := by
  rw [Iso.inv_comp_eq, ← upperStarTensorComplexHom_braiding_assoc, ← Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

open DerivedCategory Functor.LaxMonoidal

attribute [local instance] DerivedCategory.braidedCategory'

set_option maxHeartbeats 2000000 in
-- the images of complexes in the homotopy category are unfolded
/-- The comparison `m : Lf^* (- ⊗ᴸ -) ⟶ Lf^* - ⊗ᴸ Lf^* -` is its own braided conjugate. -/
lemma leftDerivedUpperStarTensor_eq_braidedConjugate :
    leftDerivedUpperStarTensor Λ f =
      braidedConjugate L((f)^*⟦Λ⟧) (leftDerivedUpperStarTensor Λ f) := by
  refine Functor.leftDerived₂_ext (leftDerivedUpperStarTensorRight Λ f)
    (leftDerivedUpperStarTensorRightCounit Λ f) (HomotopyCategory.quasiIso _ _)
    (HomotopyCategory.quasiIso _ _) _ _ _ ?_
  rw [leftDerivedUpperStarTensor_fac]
  ext P Q
  obtain ⟨A, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  obtain ⟨B, rfl⟩ := HomotopyCategory.quotient_obj_surjective Q
  symm
  simp only [NatTrans.comp_app]
  rw [leftDerivedUpperStarTensorRightCounit_app_app_eq_tensorHom,
    leftDerivedUpperStarTensorLeftCounit_app_app]
  set P := (HomotopyCategory.quotient _ (.up ℤ)).obj A with hP
  set Q := (HomotopyCategory.quotient _ (.up ℤ)).obj B with hQ
  set FP := ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj P with hFP
  set FQ := ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj Q with hFQ
  have he : (β_ (Qh.obj P) (Qh.obj Q)).hom ≫ μ Qh Q P = μ Qh P Q ≫ Qh.map (β_ P Q).hom :=
    DerivedMonoidal.braiding_hom_μ Qh (HomotopyCategory.quasiIso _ (.up ℤ)) P Q
  have hb₀ : (β_ (Qh.obj FP) (Qh.obj FQ)).hom ≫ μ Qh FQ FP = μ Qh FP FQ ≫ Qh.map (β_ FP FQ).hom :=
    DerivedMonoidal.braiding_hom_μ Qh (HomotopyCategory.quasiIso _ (.up ℤ)) FP FQ
  have hb : (β_ (Qh.obj FP) (Qh.obj FQ)).inv ≫ μ Qh FP FQ = μ Qh FQ FP ≫ Qh.map (β_ FP FQ).inv := by
    rw [Iso.inv_comp_eq, reassoc_of% hb₀, ← Qh.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hc : Qh.map (β_ FP FQ).inv ≫
        Qh.map ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ f A B)) =
      Qh.map ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ f B A)) ≫
        Qh.map (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).map (β_ P Q).inv) := by
    have h := congrArg (HomotopyCategory.quotient _ (.up ℤ)).map
      (braiding_inv_upperStarTensorComplexHom Λ f A B)
    rw [Functor.map_comp, Functor.map_comp] at h
    rw [← Qh.map_comp, ← Qh.map_comp]
    exact congrArg Qh.map h
  have hd := leftDerivedUpperStarTensor_app_app_comp Λ f Q P
  have hf := (f)^*⟦Λ⟧.leftDerivedFunctorCounit.naturality (β_ P Q).hom
  have hg : Qh.map (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).map (β_ P Q).hom) ≫
      Qh.map (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).map (β_ P Q).inv) = 𝟙 _ := by
    rw [← Qh.map_comp, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
  rw [Functor.whiskeringLeft₂_obj_obj_map_app_app, braidedConjugate_app_app, Category.assoc,
    Category.assoc]
  exact braidedConjugate_aux L((f)^*⟦Λ⟧) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb hc hd he hf hg

/-- **The derived pullback of module objects is braided**: the tensor comparison
`m_{K,M} : Lf^* (K ⊗ᴸ M) ⟶ Lf^* K ⊗ᴸ Lf^* M` is compatible with the Koszul braidings of the derived
tensor products. -/
@[reassoc]
lemma leftDerivedUpperStarTensor_braiding
    (K M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    ((leftDerivedUpperStarTensor Λ f).app K).app M ≫
        (β_ (L((f)^*⟦Λ⟧).obj K) (L((f)^*⟦Λ⟧).obj M)).hom =
      L((f)^*⟦Λ⟧).map (β_ K M).hom ≫ ((leftDerivedUpperStarTensor Λ f).app M).app K :=
  δ_braiding_of_eq _ (leftDerivedUpperStarTensor_eq_braidedConjugate Λ f) K M

end AlgebraicGeometry.ProEtale.CondensedRing
