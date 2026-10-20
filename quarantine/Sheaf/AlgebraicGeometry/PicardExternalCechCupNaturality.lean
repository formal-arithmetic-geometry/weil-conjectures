/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCechCupComponent

/-! # External Alexander--Whitney coefficient naturality
Source: Stacks Project, Tags 0BED and 07MB.
(blueprint: lem-sc-picard-external-cech-cup-naturality).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

private lemma scalarCech_map_apply
    (f : X ⟶ Spec (CommRingCat.of k)) {ι : Type w} (U : ι → X.Opens)
    {F G : X.Modules} (a : F ⟶ G) (n : ℕ)
    (s : ((picardCechFunctor f U).obj F).X n) (y : Fin (n + 1) → ι) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f G) n
        (((picardCechFunctor f U).map a).f n s) y =
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
-- Scalar Cech and tensor-total coordinate identifications require extra unification.
/-- Cochain maps with the external cup coordinates commute with right coefficients.
Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech and
following coefficient diagram; Cohomology, Tag 07MB.
(blueprint: lem-sc-picard-external-cech-cup-naturality).
Proof: Test the equality after each total-summand inclusion, then on pure tensors,
then on each product tuple. The Cech coefficient map is pointwise on tuples.
Naturality of the pullback adjunction unit moves the coefficient morphism through
the pulled-back back-face section. Presheaf restriction naturality moves it
through restriction, and tensor-section naturality moves it through the final
pairing. The front factor stays fixed. The two coordinate hypotheses thus give
identical sections. Pure tensors generate the tensor module, the summand maps are
jointly epimorphic by the coproduct universal property, and the coordinate
projections are jointly monomorphic by the product universal property. This
proves equality in every degree and hence of cochain maps. Empty index sets and
zero modules satisfy the same extensionality arguments. -/
theorem picardExternalCechCupComponent_naturality
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules)
    {G H : Y.Modules} (a : G ⟶ H)
    (cG : HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) ⟶
      (picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G))
    (cH : HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj H) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) ⟶
      (picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F H))
    (hG : IsPicardExternalCechCupComponent f g U V F G cG)
    (hH : IsPicardExternalCechCupComponent f g U V F H cH) :
    HomologicalComplex.mapBifunctorMap (𝟙 _) ((picardCechFunctor g V).map a)
        (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℕ) ≫ cH =
      cG ≫ (picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).map
        ((tensorLeft ((tensorPullback (pullback.fst f g)).obj F)).map
          ((tensorPullback (pullback.snd f g)).map a)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  subst n
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.id_f]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x z
  let W : ι × κ → (Limits.pullback f g).Opens :=
    fun ij ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2
  let τ := (tensorLeft ((tensorPullback (pullback.fst f g)).obj F)).map
    ((tensorPullback (pullback.snd f g)).map a)
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv W
    (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F H))
      (p + q)).injective
  funext y
  change TopCat.Presheaf.cechComplexFunctorXAddEquiv W
      (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F H))
      (p + q) (cH.f (p + q)
        (HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
          ((picardCechFunctor g V).obj H) (curriedTensor (ModuleCat.{w} k))
            (ComplexShape.up ℕ) p q (p + q) rfl
              (x ⊗ₜ[k] (((picardCechFunctor g V).map a).f q z)))) y =
    TopCat.Presheaf.cechComplexFunctorXAddEquiv W
      (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F H))
      (p + q) (((picardCechFunctor (pullback.fst f g ≫ f) W).map τ).f (p + q)
        (cG.f (p + q)
          (HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
            ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
              (ComplexShape.up ℕ) p q (p + q) rfl (x ⊗ₜ[k] z)))) y
  erw [scalarCech_map_apply, hH, hG, scalarCech_map_apply]
  change tmulSection _ _ =
    (_ ◁ ((tensorPullback (pullback.snd f g)).map a)).app _ (tmulSection _ _)
  rw [whiskerLeft_app_tmulSection]
  congr 1
  let Q := ⨅ l, V (y (cupBack p q l)).2
  let v := TopCat.Presheaf.cechComplexFunctorXAddEquiv V (scalarPresheaf g G) q z
    (fun l ↦ (y (cupBack p q l)).2)
  have hu := (Classical.choose
    (exists_tensorPullbackAdjunction (pullback.snd f g))).unit_naturality a
  have hs := congrArg (fun t ↦ t.val.app (op Q) v) hu
  have hle : (⨅ l, W (y l)) ≤ pullback.snd f g ⁻¹ᵁ Q := by
    intro t ht
    change (pullback.snd f g).base t ∈ ⨅ l, V (y (cupBack p q l)).2
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    intro l
    exact (iInf_le (fun j ↦ W (y j)) (cupBack p q l) ht).2
  have hn := Hom.app_presheaf_map ((tensorPullback (pullback.snd f g)).map a)
    (homOfLE hle)
    ((((Classical.choose (exists_tensorPullbackAdjunction
      (pullback.snd f g))).unit.app G).val.app (op Q)) v)
  exact (congrArg (((tensorPullback (pullback.snd f g)).obj H).presheaf.map
    (homOfLE hle).op) hs.symm).trans hn.symm

end
end AlgebraicGeometry.Scheme.Modules
