/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # The additive ideal image is the pushforward of the relative additive kernel.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

-- Affine opens of each etale test scheme suffice: base changes of a closed immersion
-- have surjective maps on global functions when their targets are affine.
set_option backward.isDefEq.respectTransparency false in
private theorem additive_restriction_epi {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] : Epi (etaleAdditiveSheafToLowerStar f) := by
  have : Sheaf.IsLocallySurjective (etaleAdditiveSheafToLowerStar f) := by
    refine ⟨fun {V} s ↦ ?_⟩
    let U := V.left.affineCover
    have hf (i : U.I₀) : Etale (U.f i ≫ V.hom) := by
      have := V.prop
      infer_instance
    let W (i : U.I₀) : Y.Etale := MorphismProperty.Over.mk ⊤ (U.f i ≫ V.hom) (hf i)
    let a (i : U.I₀) : W i ⟶ V := MorphismProperty.Over.homMk (U.f i) rfl
    refine Y.smallEtaleTopology.superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff a).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      have : IsAffine ((𝟭 Scheme).obj (W i).left) := inferInstanceAs (IsAffine (U.X i))
      obtain ⟨t, ht⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine
        (pullback.fst (W i).hom f)).2
        ((((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj X.etaleAdditiveSheaf).obj.map
          (a i).op s).down)
      refine ⟨ULift.up t, ?_⟩
      apply ULift.ext
      exact ht
    · exact U.iUnion_range
  exact Sheaf.epi_of_isLocallySurjective _

-- Restriction agrees with the canonical composition isomorphism of pushforwards.
private theorem additive_restriction_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hh : h = f ≫ g) :
    etaleAdditiveSheafToLowerStar g ≫
        (Etale.lowerStar AddCommGrpCat.{u + 1} g).map
          (etaleAdditiveSheafToLowerStar f) ≫
        (Etale.lowerStarComp AddCommGrpCat.{u + 1} f g h hh).hom.app
          X.etaleAdditiveSheaf = etaleAdditiveSheafToLowerStar h := by
  ext V : 3
  change etaleAdditiveCoefficients.map _ ≫ etaleAdditiveCoefficients.map _ ≫
      etaleAdditiveCoefficients.map _ = etaleAdditiveCoefficients.map _
  simp only [← Functor.map_comp]
  congr 1
  change (pullback.fst V.unop.hom g).appTop ≫
      (pullback.fst (pullback.snd V.unop.hom g) f).appTop ≫
      (((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        f g h hh).hom.app V.unop).left).appTop = (pullback.fst V.unop.hom h).appTop
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
  subst h
  simpa only [Category.assoc] using congrArg Scheme.Hom.appTop
    (MorphismProperty.Over.pullbackComp_left_fst_fst (P := @Etale) (Q := ⊤) f g V.unop)

-- The map from the first kernel to the second is the pullback of the epimorphism f.
-- Its epi-mono factorization therefore exhibits the second kernel as the image.
private theorem image_kernel_factor {C : Type*} [Category C] [Abelian C]
    {A B D E : C} (f : A ⟶ B) (g : B ⟶ D) (k : A ⟶ E) (i : D ≅ E)
    (hk : f ≫ g ≫ i.hom = k) [Epi f] :
    Nonempty (image (kernel.ι k ≫ f) ≅ kernel g) := by
  have hz : (kernel.ι k ≫ f) ≫ g = 0 := by
    apply (cancel_mono i.hom).mp
    simp only [Category.assoc, hk, kernel.condition, zero_comp]
  let e := kernel.lift g (kernel.ι k ≫ f) hz
  have he : e ≫ kernel.ι g = kernel.ι k ≫ f := kernel.lift_ι _ _ _
  have hp : IsLimit (PullbackCone.mk (kernel.ι k) e he.symm) := by
    refine PullbackCone.IsLimit.mk he.symm
      (fun s ↦ kernel.lift k s.fst ?_) (fun s ↦ kernel.lift_ι _ _ _) ?_ ?_
    · rw [← hk, ← Category.assoc, s.condition, Category.assoc,
        kernel.condition_assoc, zero_comp, comp_zero]
    · intro s
      apply (cancel_mono (kernel.ι g)).mp
      simp only [Category.assoc, he, kernel.lift_ι_assoc]
      exact s.condition
    · intro s m hm _
      apply (cancel_mono (kernel.ι k)).mp
      rw [hm, kernel.lift_ι]
  have : Epi e := Abelian.epi_snd_of_isLimit f (kernel.ι g) hp
  have : StrongEpi e := strongEpi_of_epi e
  exact ⟨(image.isoStrongEpiMono e (kernel.ι g) he).symm⟩

/-- The additive ideal image is the pushforward of the relative additive kernel. -/
theorem nonempty_idealAdditiveImageRelativeKernelIso (X : Scheme.{u})
    (I J : X.IdealSheafData) (hJI : J ≤ I) :
    Nonempty (image (kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) ≫
        etaleAdditiveSheafToLowerStar J.subschemeι) ≅
      (Etale.lowerStar AddCommGrpCat.{u + 1} J.subschemeι).obj
        (kernel (etaleAdditiveSheafToLowerStar (IdealSheafData.inclusion hJI)))) := by
  let F := Etale.lowerStar AddCommGrpCat.{u + 1} J.subschemeι
  let r := etaleAdditiveSheafToLowerStar (IdealSheafData.inclusion hJI)
  let c := (Etale.lowerStarComp AddCommGrpCat.{u + 1}
    (IdealSheafData.inclusion hJI) J.subschemeι I.subschemeι
    (IdealSheafData.inclusion_subschemeι hJI).symm).app I.subscheme.etaleAdditiveSheaf
  have : Epi (etaleAdditiveSheafToLowerStar J.subschemeι) :=
    additive_restriction_epi J.subschemeι
  obtain ⟨e⟩ := image_kernel_factor (etaleAdditiveSheafToLowerStar J.subschemeι)
    (F.map r) (etaleAdditiveSheafToLowerStar I.subschemeι) c
    (additive_restriction_comp _ _ _ _)
  exact ⟨e ≪≫ (PreservesKernel.iso F r).symm⟩

end AlgebraicGeometry.Scheme
