/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Defs

/-! # Fpqc descent for the normalized Picard functor

Source: Stacks Project, Tags 0D28, 0D2B and 023T.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable {X S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 500000 in
-- Constructing the comparison of two module descent data involves several pseudofunctors.
private theorem exists_iso_tensorObj_of_fpqc_local_eq (f : X ⟶ S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (pullback.snd f T.hom)))
    {T : Over S} {ι : Type*} {T' : ι → Over S} (g : ∀ i, T' i ⟶ T)
    (hgT : Sieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (g i).left) ∈
      fpqcTopology T.left)
    (L L' : (pullback f T.hom).Pic)
    (heq : ∀ i, Pic.map (baseChangeMap f (g i)) L =
      Pic.map (baseChangeMap f (g i)) L') :
    ∃ N : T.left.Pic, Nonempty ((fromSkeleton _).obj L.val ≅ (fromSkeleton _).obj L'.val ⊗
      (Modules.pullback (pullback.snd f T.hom)).obj ((fromSkeleton _).obj N.val)) := by
  have hbij (Y : Over S) : Function.Bijective (pullback.snd f Y.hom).appTop :=
    have := hf Y
    bijective_appTop_of_isIso_pushforwardUnitMap _
  have hgX : Sieve.ofArrows _ (fun i ↦ baseChangeMap f (g i)) ∈
      fpqcTopology (pullback f T.hom) := by
    rw [Sieve.ofArrows_eq_pullback_of_isPullback (fun i ↦ (g i).left)
      (fun i ↦ isPullback_baseChangeMap f (g i))]
    exact fpqcTopology.pullback_stable _ hgT
  let A := (fromSkeleton _).obj L.val
  let B := (fromSkeleton _).obj L'.val
  have := L.isInvertible
  have := L'.isInvertible
  have := Modules.IsInvertible.of_sheafOfModules A
  have := Modules.IsInvertible.of_sheafOfModules B
  obtain ⟨eB⟩ := Modules.nonempty_tensorObj_dual_iso_unit B
  let K := A ⊗ Modules.dual B
  let P : (pullback f T.hom).Modules :=
    (Modules.pullback (pullback.snd f T.hom)).obj (𝟙_ T.left.Modules)
  have eK (i : ι) : Nonempty ((Modules.pullback (baseChangeMap f (g i))).obj K ≅
      (Modules.pullback (baseChangeMap f (g i))).obj P) := by
    obtain ⟨eAB⟩ := Pic.eq_iff_nonempty_iso.1 (heq i)
    exact ⟨(Modules.nonempty_pullback_tensorObj_iso _ _ _).some ≪≫
      (((fromSkeletonToSkeletonIso _).symm ≪≫ eAB ≪≫ fromSkeletonToSkeletonIso _) ⊗ᵢ
        Iso.refl _) ≪≫ (Modules.nonempty_pullback_tensorObj_iso _ _ _).some.symm ≪≫
      (Modules.pullback _).mapIso eB ≪≫ Modules.pullbackObjUnitIso _ ≪≫
      (Modules.pullbackObjUnitIso _).symm ≪≫
      (Modules.pullback _).mapIso (Modules.pullbackObjUnitIso _).symm⟩
  -- Hence the descent datum of `𝒦` is a twist of that of `f_T^* 𝒪_T` by a cocycle `c`.
  have hD₂ (i : ι) : Modules.IsInvertible (X := pullback f (T' i).hom)
      (((modulesPseudofunctor.toDescentData fun i ↦ baseChangeMap f (g i)).obj P).obj i) :=
    inferInstanceAs ((Modules.pullback (baseChangeMap f (g i))).obj P).IsInvertible
  obtain ⟨cX, ⟨eKD⟩⟩ := DescentCocycle.exists_iso_twist
    (D₁ := (modulesPseudofunctor.toDescentData fun i ↦ baseChangeMap f (g i)).obj K)
    (D₂ := (modulesPseudofunctor.toDescentData fun i ↦ baseChangeMap f (g i)).obj P) eK
  -- The cocycle comes from `T`; the twisted descent datum of `𝒪_T` is effective.
  let cT := cX.ofBaseChange (f := f) (g := g) hbij
  let DT := cT.twist ((modulesPseudofunctor.toDescentData fun i ↦ (g i).left).obj
    (𝟙_ T.left.Modules))
  obtain ⟨N, -, ⟨eN⟩⟩ := exists_isQuasicoherent_toDescentData_iso _ hgT DT fun i ↦
    inferInstanceAs ((Modules.pullback (g i).left).obj (𝟙_ T.left.Modules)).IsQuasicoherent
  have : SheafOfModules.IsInvertible.{u, u, u} (N : T.left.Modules) :=
    isInvertible_of_toDescentData_iso _ hgT DT N ⟨eN⟩ fun i ↦
      Modules.IsInvertible.sheafOfModules_isInvertible
        ((Modules.pullback (g i).left).obj (𝟙_ T.left.Modules))
  let N' : T.left.Modules := N
  have := Modules.IsInvertible.of_sheafOfModules N'
  -- The descent data of `f_T^* 𝒩` and of `𝒦` agree, hence `f_T^* 𝒩 ≅ 𝒦`.
  have w (i : ι) : pullback.snd f (T' i).hom ≫ (g (id i)).left =
      baseChangeMap f (g i) ≫ pullback.snd f T.hom :=
    (baseChangeMap_snd f (g i)).symm
  let E :=
    ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso modulesPseudofunctor
      (f := fun i ↦ (g i).left)
      (f' := fun i ↦ baseChangeMap f (g i)) (p := pullback.snd f T.hom)
      (p' := fun i ↦ pullback.snd f (T' i).hom) (α := id) w).app
      N).symm ≪≫
    (Pseudofunctor.DescentData.pullFunctor modulesPseudofunctor (f := fun i ↦ (g i).left)
      (f' := fun i ↦ baseChangeMap f (g i)) (p := pullback.snd f T.hom)
      (p' := fun i ↦ pullback.snd f (T' i).hom) (α := id) w).mapIso eN ≪≫
    eqToIso (cT.pullFunctor_obj_twist
      (f' := fun i ↦ baseChangeMap f (g i)) (p := pullback.snd f T.hom)
      (p' := fun i ↦ pullback.snd f (T' i).hom) (α := id) w _) ≪≫
    (cT.pull (f' := fun i ↦ baseChangeMap f (g i))
      (p := pullback.snd f T.hom)
      (p' := fun i ↦ pullback.snd f (T' i).hom) (α := id) w).twistFunctor.mapIso
      ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso modulesPseudofunctor
      (f := fun i ↦ (g i).left)
      (f' := fun i ↦ baseChangeMap f (g i)) (p := pullback.snd f T.hom)
      (p' := fun i ↦ pullback.snd f (T' i).hom) (α := id) w).app _) ≪≫
    eqToIso (congrArg (fun c ↦ DescentCocycle.twist c _)
      (cX.pull_ofBaseChange (f := f) (g := g) hbij)) ≪≫
    eKD.symm
  obtain ⟨eNK⟩ := nonempty_iso_of_toDescentData_iso _ hgX
    (inferInstanceAs ((Modules.pullback (pullback.snd f T.hom)).obj N').IsQuasicoherent)
    (inferInstanceAs K.IsQuasicoherent) E
  refine ⟨Pic.mk N', ⟨?_⟩⟩
  exact (ρ_ A).symm ≪≫ whiskerLeftIso A (eB.symm ≪≫ β_ B _) ≪≫ (α_ A _ B).symm ≪≫
    β_ K B ≪≫ whiskerLeftIso B (eNK.symm ≪≫
      (Modules.pullback _).mapIso (fromSkeletonToSkeletonIso N').symm)

/-
/-- Normalized Picard classes form an fpqc sheaf when the structure sheaf is universally
its own pushforward. For existence, normalize overlap isomorphisms to preserve the chosen
trivializations along the section. Global units come from the base, so these isomorphisms
are unique and satisfy the cocycle equation. Effective fpqc descent gives an invertible
module; twisting by the inverse of its section pullback makes it normalized. For uniqueness,
local isomorphisms between two modules express their quotient as a module from the base by
fpqc descent of the scalar cocycle. Normalization then forces their classes to agree.
Source: Stacks Project, Tags 0D28, 0D2B and 023T.
(blueprint: lem-pd-normalized-picard-fpqc) -/
private theorem isSheaf_fpqc_picardFunctorNormalized_local (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom))) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      (picardFunctorNormalized f σ hσ).toFunctor := by
  have hsurj (Y : Over S) : Function.Surjective (pullback.snd f Y.hom).appTop :=
    have := hf Y
    surjective_appTop_of_isIso_pushforwardUnitMap _
  rw [isSheaf_iff_isSheaf_of_type]
  intro T R hR
  obtain ⟨ι, T', g, rfl⟩ := R.exists_eq_ofArrows
  have hR' : Sieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (g i).left) ∈
      fpqcTopology T.left := by
    simpa only [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] using hR
  rw [← Presieve.isSheafFor_iff_generate]
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  refine existsUnique_of_exists_of_unique ?_ ?_
  · -- The modules `ℒ i` and the trivialisations of their pullbacks along the sections.
    let L (i : ι) : (pullback f (T' i).hom).Modules := (fromSkeleton _).obj (x i).1.val
    have hL (i : ι) : (L i).IsInvertible :=
      have := (x i).1.isInvertible
      Modules.IsInvertible.of_sheafOfModules (L i)
    let α (i : ι) : (Modules.pullback (sectionBaseChange f σ hσ (T' i))).obj (L i) ≅
        (Modules.pullback (g i).left).obj (SheafOfModules.unit T.left.ringCatSheaf) :=
      (Pic.nonempty_iso_unit_of_map_eq _ (x i).2).some ≪≫ (Modules.pullbackObjUnitIso _).symm
    -- The isomorphisms on the double overlaps.
    have hxij (i j : ι) : Pic.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₁ (x i).1 =
        Pic.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₂ (x j).1 :=
      congrArg Subtype.val (hx i j _ (pullback.fst _ _) (pullback.snd _ _) pullback.condition)
    let e (i j : ι) : (Modules.pullback (chosenPullbackBaseChangeMap f (g i) (g j)).p₁).obj (L i) ≅
        (Modules.pullback (chosenPullbackBaseChangeMap f (g i) (g j)).p₂).obj (L j) :=
      (fromSkeletonToSkeletonIso _).symm ≪≫ (Pic.eq_iff_nonempty_iso.1 (hxij i j)).some ≪≫
        fromSkeletonToSkeletonIso _
    let D := normalizedDescentData (sectionBaseChange_snd f σ hσ)
      (sectionBaseChange_comp_baseChangeMap f σ hσ) hsurj (L := L) α e
    -- The family `X_{T i} ⟶ X_T` is an fpqc covering.
    have hg : Sieve.ofArrows _ (fun i ↦ baseChangeMap f (g i)) ∈
        fpqcTopology (pullback f T.hom) := by
      rw [Sieve.ofArrows_eq_pullback_of_isPullback (fun i ↦ (g i).left)
        (fun i ↦ isPullback_baseChangeMap f (g i))]
      exact fpqcTopology.pullback_stable _ hR'
    obtain ⟨M, -, ⟨eM⟩⟩ := exists_isQuasicoherent_toDescentData_iso _ hg D.descentData
      (fun i ↦ inferInstanceAs (L i).IsQuasicoherent)
    have : SheafOfModules.IsInvertible.{u, u, u} (M : (pullback f T.hom).Modules) :=
      isInvertible_of_toDescentData_iso _ hg D.descentData M ⟨eM⟩
        (fun i ↦ Modules.IsInvertible.sheafOfModules_isInvertible (L i))
    let M' : (pullback f T.hom).Modules := M
    have hM : M'.IsInvertible := Modules.IsInvertible.of_sheafOfModules _
    -- `M` restricts to `ℒ i` on `X_{T i}`.
    let eMi (i : ι) : (Modules.pullback (baseChangeMap f (g i))).obj M' ≅ L i :=
      { hom := eM.hom.hom i
        inv := eM.inv.hom i
        hom_inv_id := by
          rw [← Pseudofunctor.DescentData.comp_hom, eM.hom_inv_id,
            Pseudofunctor.DescentData.id_hom]
          rfl
        inv_hom_id := by
          rw [← Pseudofunctor.DescentData.comp_hom, eM.inv_hom_id,
            Pseudofunctor.DescentData.id_hom]
          rfl }
    -- Twist `M` by the pullback of an inverse `N'` of `σ_T^* M`.
    let Mσ := (Modules.pullback (sectionBaseChange f σ hσ T)).obj M'
    obtain ⟨eN'⟩ := Modules.nonempty_tensorObj_dual_iso_unit Mσ
    let M₁ := M' ⊗ (Modules.pullback (pullback.snd f T.hom)).obj (Modules.dual Mσ)
    have : SheafOfModules.IsInvertible.{u, u, u} M₁ :=
      Modules.IsInvertible.sheafOfModules_isInvertible M₁
    refine ⟨⟨Pic.mk M₁, Pic.eq_iff_nonempty_iso.2 ⟨fromSkeletonToSkeletonIso _ ≪≫
      (Modules.pullback _).mapIso (fromSkeletonToSkeletonIso M₁) ≪≫
      (Modules.nonempty_pullback_tensorObj_iso _ _ _).some ≪≫
      (Iso.refl Mσ ⊗ᵢ pullbackSectionBaseChangeSndIso f σ hσ T _) ≪≫ eN' ≪≫
      (fromSkeletonToSkeletonIso _).symm⟩⟩, fun i ↦ Subtype.ext ?_⟩
    -- On `T i`, the pullback of `σ_T^* M` is `σ_{T i}^* ℒ i`, which is trivial; hence so is the
    -- pullback of its inverse.
    let A : (Modules.pullback (g i).left).obj Mσ ≅ SheafOfModules.unit _ :=
      (Modules.pullbackComp _ _).app M' ≪≫
        (Modules.pullbackCongr (sectionBaseChange_comp_baseChangeMap f σ hσ (g i)).symm).app M' ≪≫
        ((Modules.pullbackComp _ _).app M').symm ≪≫ (Modules.pullback _).mapIso (eMi i) ≪≫
        (Pic.nonempty_iso_unit_of_map_eq _ (x i).2).some
    let E : (Modules.pullback (g i).left).obj (Modules.dual Mσ) ≅ SheafOfModules.unit _ :=
      (λ_ _).symm ≪≫ (A.symm ⊗ᵢ Iso.refl _) ≪≫
        (Modules.nonempty_pullback_tensorObj_iso _ _ _).some.symm ≪≫
        (Modules.pullback _).mapIso eN' ≪≫ Modules.pullbackObjUnitIso _
    exact Pic.eq_iff_nonempty_iso.2 ⟨fromSkeletonToSkeletonIso _ ≪≫
      (Modules.pullback _).mapIso (fromSkeletonToSkeletonIso M₁) ≪≫
      (Modules.nonempty_pullback_tensorObj_iso _ _ _).some ≪≫
      (eMi i ⊗ᵢ ((Modules.pullbackComp _ _).app _ ≪≫
        (Modules.pullbackCongr (Limits.pullback.lift_snd _ _ _)).app _ ≪≫
        ((Modules.pullbackComp _ _).app _).symm ≪≫ (Modules.pullback _).mapIso E ≪≫
        Modules.pullbackObjUnitIso _)) ≪≫ ρ_ _⟩
  · intro t t' ht ht'
    obtain ⟨N, ⟨e⟩⟩ := exists_iso_tensorObj_of_fpqc_local_eq f hf g hR' t.1 t'.1
      (fun i ↦ congrArg Subtype.val ((ht i).trans (ht' i).symm))
    exact picardFunctorNormalized_eq_of_iso_tensorObj f σ hσ t t' _ ((fromSkeleton _).obj N.val)
      (SheafOfModules.unit _) e
      ((ρ_ _).symm ≪≫ whiskerLeftIso _ (Modules.pullbackObjUnitIso _).symm)

-/

end AlgebraicGeometry
