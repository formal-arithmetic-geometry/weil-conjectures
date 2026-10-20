/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.PicardLeftCechCupComponent

/-! # Left-coefficient naturality of the external Cech cup

Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech;
Cohomology, Tags 01FD and 07MB.
(blueprint: lem-sc-picard-left-cech-cup-naturality).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct DirectSum
open Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

private lemma scalarCech_map_apply
    (f : X ⟶ Spec (CommRingCat.of k)) {ι : Type w} (U : ι → X.Opens)
    {F G : X.Modules} (a : F ⟶ G) (n : ℕ)
    (s : ((picardScalarCechFunctor f U).obj F).X n) (y : Fin (n + 1) → ι) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f G) n
        (((picardScalarCechFunctor f U).map a).f n s) y =
      a.app (⨅ l, U (y l))
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f F) n s y) := by
  change TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f G) n
    (((cechComplexFunctor U).map (scalarHom f a).hom).f n s) y = _
  rw [TopCat.Presheaf.cechComplexFunctorXAddEquiv_apply,
    TopCat.Presheaf.cechComplexFunctorXAddEquiv_apply]
  have h := ConcreteCategory.congr_hom
    (TopCat.Presheaf.cechComplexFunctor_map_f_π U (scalarPresheaf f F) (scalarHom f a).hom n y) s
  simp only [ConcreteCategory.comp_apply] at h
  erw [h]
  exact (NatTrans.naturality_apply (scalarHom f a).hom
    (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op _).symm


set_option maxHeartbeats 800000 in
-- Tensor-total and extension coordinate identifications require extra unification.
/-- Extended cup components commute with left coefficient maps.
Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech and
its following coefficient diagram; Cohomology, Tag 07MB.
(blueprint: lem-sc-picard-left-cech-cup-naturality).

Proof: In each degree test after the total-summand inclusions. If either
bidegree is negative its tensor factor is zero. Otherwise use the extension
isomorphisms, test on pure tensors and each product tuple, and apply the two
coordinate hypotheses. The scalar Cech map acts by the coefficient morphism
on each section. Naturality of the first-projection pullback adjunction unit
moves that morphism through the front-face pullback; restriction naturality
moves it through restriction, and tensor-section naturality moves it through
the final tensor. The second factor is fixed. Thus the two sections agree.
Tensor, coproduct and product extensionality finish the equality. Empty covers
and zero modules obey the same extensionality arguments. -/
theorem picardLeftCechCupComponent_naturality
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] (G : Y.Modules)
    {F H : X.Modules} (a : F ⟶ H)
    (cF : (picardLeftTensorCechFunctor f g G).obj F ⟶
      (picardLeftProductCechFunctor f g G).obj F)
    (cH : (picardLeftTensorCechFunctor f g G).obj H ⟶
      (picardLeftProductCechFunctor f g G).obj H)
    (hF : IsPicardLeftCechCupComponent f g F G cF)
    (hH : IsPicardLeftCechCupComponent f g H G cH) :
    (picardLeftTensorCechFunctor f g G).map a ≫ cH =
      cF ≫ (picardLeftProductCechFunctor f g G).map a  := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  by_cases hp : ∃ i : ℕ, (i : ℤ) = p
  · obtain ⟨p, rfl⟩ := hp
    by_cases hq : ∃ j : ℕ, (j : ℤ) = q
    · obtain ⟨q, rfl⟩ := hq
      change (p : ℤ) + (q : ℤ) = n at hpq
      have hn : n = ((p + q : ℕ) : ℤ) := by omega
      subst n
      let A := (picardScalarCechFunctor f (picardFiniteAffineOpens X)).obj F
      let B := (picardScalarCechFunctor g (picardFiniteAffineOpens Y)).obj G
      let C := (picardScalarCechFunctor (pullback.fst f g ≫ f)
        (picardProductAffineOpens f g)).obj (externalCupCoefficients f g H G)
      rw [← cancel_mono (C.extendXIso ComplexShape.embeddingUpNat
        (show ((p + q : ℕ) : ℤ) = ((p + q : ℕ) : ℤ) from rfl)).hom]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x z
      obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective
        (A.extendXIso ComplexShape.embeddingUpNat rfl).inv).mp inferInstance x
      obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
        (B.extendXIso ComplexShape.embeddingUpNat rfl).inv).mp inferInstance z
      simp only [HomologicalComplex.comp_f, Category.assoc]
      change ModuleCat.Hom.hom
        (HomologicalComplex.ιMapBifunctor (A.extend ComplexShape.embeddingUpNat)
          (B.extend ComplexShape.embeddingUpNat) (curriedTensor _) (ComplexShape.up ℤ)
          (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ) _ ≫
          (HomologicalComplex.mapBifunctorMap
            (HomologicalComplex.extendMap
              ((picardScalarCechFunctor f (picardFiniteAffineOpens X)).map a)
                ComplexShape.embeddingUpNat)
            (𝟙 (B.extend ComplexShape.embeddingUpNat)) (curriedTensor _)
              (ComplexShape.up ℤ)).f _ ≫ _ ≫ _) _ = _
      rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
      simp only [HomologicalComplex.id_f, curriedTensor_map_app,
        curriedTensor_obj_map, whiskerLeft_id]
      rw [HomologicalComplex.extendMap_f _ _ (show (p : ℤ) = (p : ℤ) from rfl)]
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.hom_whiskerRight]
      erw [ModuleCat.hom_id, LinearMap.id_apply (R := k),
        LinearMap.rTensor_tmul]
      simp only [LinearMap.comp_apply]
      have he := ConcreteCategory.congr_hom
        (A.extendXIso ComplexShape.embeddingUpNat
          (show (p : ℤ) = (p : ℤ) from rfl)).inv_hom_id x
      dsimp at he
      erw [he]
      let τ := (tensorRight ((tensorPullback (pullback.snd f g)).obj G)).map
        ((tensorPullback (pullback.fst f g)).map a)
      let C₀ := (picardScalarCechFunctor (pullback.fst f g ≫ f)
        (picardProductAffineOpens f g)).obj (externalCupCoefficients f g F G)
      have hprod (v : (C₀.extend ComplexShape.embeddingUpNat).X ((p + q : ℕ) : ℤ)) :
          (C.extendXIso ComplexShape.embeddingUpNat rfl).hom
            (((picardLeftProductCechFunctor f g G).map a).f ((p + q : ℕ) : ℤ) v) =
          ((picardScalarCechFunctor (pullback.fst f g ≫ f)
            (picardProductAffineOpens f g)).map τ).f (p + q)
              ((C₀.extendXIso ComplexShape.embeddingUpNat rfl).hom v) := by
        change (C.extendXIso ComplexShape.embeddingUpNat rfl).hom
          ((HomologicalComplex.extendMap
            ((picardScalarCechFunctor (pullback.fst f g ≫ f)
              (picardProductAffineOpens f g)).map τ) ComplexShape.embeddingUpNat).f _ v) = _
        rw [HomologicalComplex.extendMap_f _ _
          (show ((p + q : ℕ) : ℤ) = ((p + q : ℕ) : ℤ) from rfl)]
        simp only [ConcreteCategory.comp_apply]
        exact ConcreteCategory.congr_hom
          (C.extendXIso ComplexShape.embeddingUpNat
            (show ((p + q : ℕ) : ℤ) = ((p + q : ℕ) : ℤ) from rfl)).inv_hom_id _
      erw [hprod]
      apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv (picardProductAffineOpens f g)
        (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g H G))
          (p + q)).injective
      funext y
      erw [hH, scalarCech_map_apply, scalarCech_map_apply, hF]
      change tmulSection _ _ =
        (((tensorPullback (pullback.fst f g)).map a) ▷ _).app _ (tmulSection _ _)
      rw [whiskerRight_app_tmulSection]
      congr 1
      let Q := ⨅ l, picardFiniteAffineOpens X (y (cupFront p q l)).1
      let v := TopCat.Presheaf.cechComplexFunctorXAddEquiv
        (picardFiniteAffineOpens X) (scalarPresheaf f F) p x
          (fun l ↦ (y (cupFront p q l)).1)
      have hu := (Classical.choose
        (exists_tensorPullbackAdjunction (pullback.fst f g))).unit_naturality a
      have hs := congrArg (fun t ↦ t.val.app (op Q) v) hu
      have hle := (picardProductCechFace f g (picardFiniteAffineOpens X)
        (picardFiniteAffineOpens Y) y (cupFront p q)).1
      have hr := Hom.app_presheaf_map ((tensorPullback (pullback.fst f g)).map a)
        (homOfLE hle)
        ((((Classical.choose (exists_tensorPullbackAdjunction
          (pullback.fst f g))).unit.app F).val.app (op Q)) v)
      exact (congrArg (((tensorPullback (pullback.fst f g)).obj H).presheaf.map
        (homOfLE hle).op) hs.symm).trans hr.symm
    · have hz := HomologicalComplex.isZero_extend_X
        ((picardScalarCechFunctor g (picardFiniteAffineOpens Y)).obj G)
        ComplexShape.embeddingUpNat q
          (fun j hj ↦ hq ⟨j, hj⟩)
      exact ((tensorLeft _).map_isZero hz).eq_of_src _ _
  · have hz := HomologicalComplex.isZero_extend_X
      ((picardScalarCechFunctor f (picardFiniteAffineOpens X)).obj F)
      ComplexShape.embeddingUpNat p
        (fun i hi ↦ hp ⟨i, hi⟩)
    exact ((tensorRight _).map_isZero hz).eq_of_src _ _

end
end AlgebraicGeometry.Scheme.Modules
