/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.PointExchangeOpen
public import WeilConjectures.TraceFormula.Specialization.SupportClosureProper
public import WeilConjectures.TraceFormula.Specialization.SupportIdentityOnComponent
public import WeilConjectures.TraceFormula.Specialization.ComponentClassReduction
public import WeilConjectures.TraceFormula.Specialization.ComponentCounitIso
public import WeilConjectures.TraceFormula.Specialization.ComponentUnitClassF
public import WeilConjectures.Tactic.MatchTactic
public import WeilConjectures.TraceFormula.Specialization.ComponentExchangeAssembly
public import WeilConjectures.TraceFormula.Specialization.PointExchangeNormalForm

/-!

# The compact-support exchanges of the deformation to the normal cone

For a correspondence `c` contracting at `y`, the compact-support exchanges of blueprint
`det-nearby-exchange-maps` (3) for the support map
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.supportCompactSupportExchange`, through
the compactification `C ⊂ C̄ ⟶ X ⨯ X` deformed along `c̄⁻¹(x, x)`) and for the structure map of `X`
(`ProEtale.CondensedRing.pointCompactSupportExchangeOfSeparated`, through a compactification
`X ⊂ X̄` and the dense compactification of the deformation of `X̄`) give the trace specialization
`deformationTraceSpecialization`. This file states that these exchanges specialize the class of
the component `B ∋ y` of the fixed locus
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.specializesComponentClass_deformation`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace Correspondence

namespace IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Algebra k k'] (F : c.FixedLocus)

set_option Elab.async false in
set_option maxHeartbeats 2000000 in
-- instantiating the support identity, facts (II) and (III) and the reduction at the concrete data
-- is slow; the auxiliary theorems of `instantiate_by_match` are checked one after the other
-- (`Elab.async false`), which keeps the memory below 4 GB
/-- **The compact-support exchanges of the deformation specialize the class of `B`** (blueprint
`det-tf-sp-theta-proper-constant`, `det-tf-sp-theta-open-constant`, with
`det-tf-fixed-deformation-points`; Varshavsky, *Lefschetz–Verdier trace formula and a
generalization of a theorem of Fujiwara*, §1.4–§2): for the exchanges `ν_c`
(`supportCompactSupportExchange`) and `ν_X` (`pointCompactSupportExchangeOfSeparated`), the
exchange `ν_F` of the fixed loci maps the specialization of the unit class of the special fixed
locus `F'` to the specialization of the class of the component `B ∋ y`. Near `y` the deformed fixed
locus is the constant family `B × S` up to nilpotents, on which `ν` is the inverse of the proper
exchange and is compatible with the specialization units. -/
theorem specializesComponentClass_deformation {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))}) :
    hc.SpecializesComponentClass k' (hc.supportCompactSupportExchange k')
      (pointCompactSupportExchangeOfSeparated (y ≫ c.c₁) k') F j := by
  have hmem : (F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k)) ∈
      Set.range j.left.base := by rw [hB]; rfl
  obtain ⟨b, hbj⟩ : ∃ b : RationalPoint B, b ≫ j = F.liftPoint y hc.comp_c₁_eq_comp_c₂ := by
    have hh : Set.range (F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base ⊆
        Set.range j.left.base := by
      rintro _ ⟨p, rfl⟩
      rwa [Subsingleton.elim (α := Spec (.of k)) p default]
    exact ⟨Over.homMk (IsOpenImmersion.lift j.left _ hh) (by
      rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w]),
      Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
  have hb : b ≫ j ≫ F.ι = y := by rw [← Category.assoc, hbj, FixedLocus.liftPoint_ι]
  have hI := hc.isIso_ΨF_map_componentCounit k' (hc.supportCompactSupportExchange k')
      (pointCompactSupportExchangeOfSeparated (y ≫ c.c₁) k') F j hmem
  have hbr : Set.range b.left.base = Set.univ := by
    refine Set.eq_univ_of_forall fun p ↦ ?_
    obtain ⟨q, hq⟩ : j.left.base p ∈ Set.range j.left.base := ⟨p, rfl⟩
    have h1 : j.left.base p ∈ ({((F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base
        (default : Spec (.of k)))} : Set _) := hB ▸ ⟨p, rfl⟩
    refine ⟨(default : Spec (.of k)), j.left.isOpenEmbedding.injective ?_⟩
    rw [Set.mem_singleton_iff] at h1
    rw [h1, ← hbj]
    rfl
  have : IsProper (deformationTotalToTrait B b.left.ker k') :=
    isProper_deformationTotalToTrait_ker B k' hbr
  have hM := (deformationModel B b.left.ker k').preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel B _ k') (deformationModel_exists_comp_ε B _ k')
  have hN := (deformationModel c.C y.left.ker k').preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel c.C _ k') (deformationModel_exists_comp_ε c.C _ k')
  have : IsProper j.left := by
    have : IsProper (j.left ≫ F.F.hom) := by rw [Over.w j]; infer_instance
    exact IsProper.of_comp _ F.F.hom
  have : IsClosedImmersion j.left := .of_isPreimmersion _ j.left.isClosedMap.isClosed_range
  have : IsClosedImmersion (j ≫ F.ι).left := by rw [Over.comp_left]; infer_instance
  have := hc.isClosedImmersion_componentSpecialLift k' j hb
  have h3 := unitClass_comp_map_comp_exchange_eq ℓ j F.ι (componentModelHom k' j hb) hM hN
    (hc.componentSpecialLift k' j hb) (hc.specialFixedLocus k').ι
    (hc.componentSpecialLift_ι k' j hb) hI
  have hD := unitClass_comp_map_comp_deformationCompactSupportExchange_app B b.left.ker k' (ℓ := ℓ)
  have hF1 := supportCompactSupportExchange_app_lowerStar_eq hc k' j hb
    (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  have hF3 := componentSupportModelHom_pushforwardExchange_app hc k' j hb
  have : IsProper (j ≫ F.d).left := by
    have : IsProper ((j ≫ F.d).left ≫ X.hom) := by rw [Over.w (j ≫ F.d)]; infer_instance
    exact IsProper.of_comp _ X.hom
  have : IsProper ((j ≫ F.d) ≫ diag X).left := by rw [Over.comp_left]; infer_instance
  have hphg : ((j ≫ F.ι).left ≫ (supportClosureι c).left) ≫
      (Limits.prod.lift (supportClosureMap c ≫ Limits.prod.fst)
        (supportClosureMap c ≫ Limits.prod.snd)).left = ((j ≫ F.d) ≫ diag X).left := by
    rw [Category.assoc, ← Over.comp_left, ← Over.comp_left,
      show supportClosureι c ≫ Limits.prod.lift (supportClosureMap c ≫ Limits.prod.fst)
        (supportClosureMap c ≫ Limits.prod.snd) = c.support by
          rw [prodLift_supportClosureMap, supportClosureι_map],
      Category.assoc, F.isPullback.w, ← Category.assoc]
  have : IsProper ((j ≫ F.ι) ≫ c.support).left := isProper_left_of_isProper_of_isSeparated _
  have : IsProper ((j ≫ F.ι) ≫ supportClosureι c).left := isProper_left_of_isProper_of_isSeparated _
  have : IsProper (((j ≫ F.ι) ≫ supportClosureι c) ≫ Limits.prod.lift
    (supportClosureMap c ≫ Limits.prod.fst) (supportClosureMap c ≫ Limits.prod.snd)).left :=
    isProper_left_of_isProper_of_isSeparated _
  have hF2 := compactificationRoute_ambient_eq_fixedSquareRoute_of_eq ℓ j (rfl : j ≫ F.ι = _)
    F.isPullback.w (supportClosureι c)
    (Limits.prod.lift (supportClosureMap c ≫ Limits.prod.fst)
      (supportClosureMap c ≫ Limits.prod.snd))
    (by rw [prodLift_supportClosureMap, supportClosureι_map])
    (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (by rw [hphg]; rfl)
  have : IsProper (hc.componentSpecialLift k' j hb ≫ (hc.specialFixedLocus k').d).left :=
    isProper_left_of_isProper_of_isSeparated _
  have : IsProper ((hc.componentSpecialLift k' j hb ≫ (hc.specialFixedLocus k').d) ≫
    diag (deformationSpecialFibre X (y ≫ c.c₁).left.ker k')).left :=
    isProper_left_of_isProper_of_isSeparated _
  have : IsProper (componentSpecialFibreMap k' j hb).left :=
    isProper_left_of_isProper_of_isSeparated _
  have : IsProper (componentSpecialFibreMap k' j hb ≫
    (hc.specialCorrespondence k').support).left := isProper_left_of_isProper_of_isSeparated _
  have : IsProper (componentSpecialFibreMap k' j hb ≫ hc.supportClosureSpecialι k').left :=
    isProper_left_of_isProper_of_isSeparated _
  have : IsProper ((componentSpecialFibreMap k' j hb ≫ hc.supportClosureSpecialι k') ≫
    supportClosureSpecialMap c y k').left := isProper_left_of_isProper_of_isSeparated _
  have : IsProper (hc.componentSpecialLift k' j hb).left :=
    isProper_left_of_isProper_of_isSeparated _
  have hphg' : ((componentSpecialFibreMap k' j hb).left ≫ (hc.supportClosureSpecialι k').left) ≫
      (supportClosureSpecialMap c y k').left = ((hc.componentSpecialLift k' j hb ≫
        (hc.specialFixedLocus k').d) ≫
          diag (deformationSpecialFibre X (y ≫ c.c₁).left.ker k')).left := by
    rw [Category.assoc, ← Over.comp_left, ← Over.comp_left, hc.supportClosureSpecialι_comp k',
      ← hc.componentSpecialLift_ι k' j hb, Category.assoc, (hc.specialFixedLocus k').isPullback.w,
      ← Category.assoc]
  have hF2' := compactificationRoute_ambient_eq_fixedSquareRoute_of_eq ℓ
    (hc.componentSpecialLift k' j hb) (hc.componentSpecialLift_ι k' j hb)
    (hc.specialFixedLocus k').isPullback.w (hc.supportClosureSpecialι k')
    (supportClosureSpecialMap c y k') (hc.supportClosureSpecialι_comp k')
    ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj
      (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) (by rw [hphg']; rfl)
  have hfsp : hc.componentSpecialLift k' j hb ≫ (hc.specialFixedLocus k').d =
      deformationSpecialFibreMap (j ≫ F.d)
        (map_siteIdeal_ker_le_of_comp_eq _ (component_comp_d_eq j hb)) k' := by
    rw [← (hc.specialFixedLocus k').ι_c₁, hc.componentSpecialLift_ι_assoc]
    change componentSpecialFibreMap k' j hb ≫ hc.specialLeg₁ k' = _
    rw [      deformationSpecialFibreMap_comp k' _ _ _ _
        (map_siteIdeal_ker_le_of_comp_eq _ (by rw [← Category.assoc, hb]))]
    exact deformationSpecialFibreMap_eq_of_eq k' _ _ (by simp only [Category.assoc, F.ι_c₁]) _
  have hXm := (deformationModel X (y ≫ c.c₁).left.ker k')
    |>.preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel X _ k') (deformationModel_exists_comp_ε X _ k')
  have hXXm := NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel (ℓ := ℓ)
      (deformationProdModel X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
      (isTraitModel_deformationProdModel X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
      (deformationProdModel_exists_comp_ε X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
  have hL := eqToHom_comp_map_lowerStarComp_inv ℓ (j ≫ F.d) (j ≫ F.d) rfl (diag X)
    (componentPointModelHom_comp_diag_left j) (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (by rw [hphg]; rfl)
  have hL' := eqToHom_comp_map_lowerStarComp_inv ℓ
    (hc.componentSpecialLift k' j hb ≫ (hc.specialFixedLocus k').d) _ hfsp
    (diag (deformationSpecialFibre X (y ≫ c.c₁).left.ker k'))
    (componentPointModelHom_comp_diag_special hc k' j hb)
    ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj
      (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) (by rw [hphg']; rfl)
  have hχg := NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_app_map ℓ
      (componentModelHom k' j hb) hM hN
  have hχΔ := NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_app_map ℓ
      (deformationDiagModelHom X (y ≫ c.c₁).left.ker k') hXm hXXm
  have hχdj := NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_app_map ℓ
      (componentPointModelHom k' j hb) hM hXm
  instantiate_by_match CategoryTheory.supportIdentity_aux [hF1 := hF1, hF3 := hF3, hF2 := hF2,
    hF2' := hF2', hL := hL, hL' := hL', hχΔ := hχΔ, hχdj := hχdj, hχg := hχg,
    t := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).hom.app (𝟙_ _),
    hι := (ObjectProperty.fullyFaithfulι (boundedConstructible (condensedRingObj
      (Profinite.padicAlgClRingObj ℓ) (deformationSpecialFibre X (y ≫ c.c₁).left.ker k' ⨯
        deformationSpecialFibre X (y ≫ c.c₁).left.ker k').left))).faithful,
    hback := NatIso.hom_app_comp_inv_app_comp_map_eqToHom
      (boundedConstructibleLowerStarComp ℓ (j ≫ F.d) (diag X)) (𝟙_ _) rfl,
    cinv := (boundedConstructibleLowerStarCompOfEq ℓ (hc.componentSpecialLift k' j hb)
      (hc.specialFixedLocus k').ι (hc.componentSpecialLift_ι k' j hb)).inv.app
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _)),
    hcinv := Iso.inv_hom_id_app (boundedConstructibleLowerStarCompOfEq ℓ
      (hc.componentSpecialLift k' j hb) (hc.specialFixedLocus k').ι
        (hc.componentSpecialLift_ι k' j hb))
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _)),
    tr := eqToHom (congrArg (fun f => (boundedConstructibleLowerStar ℓ f).obj
      ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _))) hfsp),
    hback' := NatIso.hom_app_comp_inv_app_comp_map_eqToHom_eq (boundedConstructibleLowerStarComp ℓ
      (hc.componentSpecialLift k' j hb ≫ (hc.specialFixedLocus k').d)
      (diag (deformationSpecialFibre X (y ≫ c.c₁).left.ker k')))
      ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _))
      (congrArg (fun f => (boundedConstructibleLowerStar ℓ f).obj
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _))) hfsp)
      (congrArg (fun f => (boundedConstructibleLowerStar ℓ f).obj
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _))) hfsp)] as hSI
  -- fact (II): the factorization of `ν_F` on `j_! ℚ̄_ℓ`
  have : IsProper (deformationSpecialFibreMap (j ≫ F.d)
      (map_siteIdeal_ker_le_of_comp_eq _ (component_comp_d_eq j hb)) k').left := by
    rw [← hfsp]; infer_instance
  have hNF := pointCompactSupportExchangeOfSeparated_app_lowerStar_normalForm (ℓ := ℓ)
    (y ≫ c.c₁) k' (j ≫ F.d) (component_comp_d_eq j hb)
  instantiate_by_match TraceSpecialization.fixedLocusToPointCompactSupportExchange_app_comp_eq_of_eq
    [h := hSI, hX := hNF] as hFPE
  have hS3 := lowerShriekCompOfEq_hom_app_comp_hom_app_comp_map_inv_comp_inv ℓ j F.d
    (toPoint X) (comp_toPoint j) (comp_toPoint F.d) (comp_toPoint (j ≫ F.d))
    (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  have hS4 := lowerShriekCompOfEq_hom_app_comp_map_comp_inv_eq ℓ
    (hc.componentSpecialLift k' j hb) (hc.specialFixedLocus k').d hfsp (toPoint _)
    (comp_toPoint (hc.componentSpecialLift k' j hb)) (comp_toPoint (hc.specialFixedLocus k').d)
    (comp_toPoint (deformationSpecialFibreMap (j ≫ F.d)
      (map_siteIdeal_ker_le_of_comp_eq _ (component_comp_d_eq j hb)) k'))
    ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _))
    (congrArg (fun f => (boundedConstructibleLowerStar ℓ f).obj
      ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj (𝟙_ _))) hfsp)
  have hac := boundedConstructibleLowerStarCompOfEq_hom_app_rfl ℓ j F.ι
    (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  instantiate_by_match CategoryTheory.exchange_app_eq_of_fixedSquare_aux
    [h := hFPE, hS3 := hS3, hS4 := hS4, hac := hac] as h1
  -- fact (III) glued to the unit class identity of `ν_B`
  instantiate_by_match CategoryTheory.comp_map_comp_comp_eq_of_eq' [h := h3, h' := hD] as h2
  -- the cancellation
  apply_by_match TraceSpecialization.specializesComponentClass_of_eq [j := j, hI := hI,
    h₁ := h1, h₂ := h2]

end IsContractingAt

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
