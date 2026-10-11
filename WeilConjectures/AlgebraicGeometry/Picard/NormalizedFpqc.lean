/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Defs

/-!
# The `σ`-normalized Picard functor satisfies fpqc descent

For a morphism of schemes `f : X ⟶ S` with a section `σ` such that `𝒪_T ⟶ f_{T,*} 𝒪_{X_T}` is an
isomorphism for every `T` over `S`, the `σ`-normalized relative Picard functor `Pic_{X/S,σ}`
satisfies the sheaf condition for fpqc coverings `{T i ⟶ T}`, and in particular for a single
faithfully flat quasi-compact morphism `T' ⟶ T`.

The proof follows `AlgebraicGeometry.isSheaf_picardFunctorNormalized`; the separatedness, which
there uses the fppf sheaf property of `Pic_{X/S}`, is instead deduced from fpqc descent of
quasi-coherent modules: two classes on `X_T` which agree on an fpqc covering differ by a class
pulled back from `T`.

## Main statements

- `AlgebraicGeometry.exists_iso_tensorObj_of_pic_map_eq`: two classes in `Pic (X_T)` which agree
  on the members of an fpqc covering of `T` differ by a class pulled back from `T`.
- `AlgebraicGeometry.isSheafFor_ofArrows_picardFunctorNormalized`: the sheaf condition for an fpqc
  covering family.
- `AlgebraicGeometry.isSheafFor_singleton_picardFunctorNormalized`: the sheaf condition for a
  single flat, surjective and quasi-compact morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable {X S : Scheme.{u}}

/-- The base change `X_{T i} ⟶ X_T` of an fpqc covering family `T i ⟶ T` is an fpqc covering. -/
lemma ofArrows_baseChangeMap_mem_fpqcTopology (f : X ⟶ S) {T : Over S} {ι : Type*}
    {T' : ι → Over S} (g : ∀ i, T' i ⟶ T)
    (hR : Presieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (g i).left) ∈
      fpqcPrecoverage T.left) :
    Sieve.ofArrows _ (fun i ↦ baseChangeMap f (g i)) ∈ fpqcTopology (pullback f T.hom) :=
  Precoverage.generate_mem_toGrothendieck
    (Precoverage.mem_coverings_of_isPullback (fun i ↦ (g i).left) hR (pullback.snd f T.hom)
      (fun i ↦ baseChangeMap f (g i)) (fun i ↦ pullback.snd f (T' i).hom)
      (fun i ↦ isPullback_baseChangeMap f (g i)))

/-- **Classes agreeing on an fpqc covering differ by a class from the base.** Assume that
`𝒪_T ⟶ f_{T,*} 𝒪_{X_T}` is an isomorphism for every `T` over `S`. If two classes
`ℒ, ℒ' ∈ Pic (X_T)` have the same pullbacks to `X_{T i}` for an fpqc covering `{T i ⟶ T}`, then
`ℒ ≅ ℒ' ⊗ f_T^* 𝒩` for an invertible `𝒪_T`-module `𝒩`: the transition functions of the
trivialisations of `ℒ ⊗ ℒ'^{-1}` on the `X_{T i}` descend to a cocycle on `{T i ⟶ T}`.

(blueprint: `lem-pc-pic-exact`) -/
theorem exists_iso_tensorObj_of_pic_map_eq (f : X ⟶ S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom))) {T : Over S}
    {ι : Type*} {T' : ι → Over S} (g : ∀ i, T' i ⟶ T)
    (hR : Presieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (g i).left) ∈
      fpqcPrecoverage T.left)
    (L L' : (Limits.pullback f T.hom).Pic)
    (heq : ∀ i, Pic.map (baseChangeMap f (g i)) L = Pic.map (baseChangeMap f (g i)) L') :
    ∃ N : T.left.Pic, Nonempty ((fromSkeleton _).obj L.val ≅ (fromSkeleton _).obj L'.val ⊗
      (Modules.pullback (Limits.pullback.snd f T.hom)).obj ((fromSkeleton _).obj N.val)) := by
  have hbij (Y : Over S) : Function.Bijective (pullback.snd f Y.hom).appTop :=
    have := hf Y
    bijective_appTop_of_isIso_pushforwardUnitMap _
  have hgT : Sieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (g i).left) ∈
      fpqcTopology T.left :=
    Precoverage.generate_mem_toGrothendieck hR
  have hgX := ofArrows_baseChangeMap_mem_fpqcTopology f g hR
  -- `𝒦 = ℒ ⊗ ℒ'^∨` is trivial on the `X_{T i}`.
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
  let cT := cX.ofBaseChange hbij
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
      (f := fun i ↦ (g i).left) (f' := fun i ↦ baseChangeMap f (g i)) w).app
      N).symm ≪≫
    (Pseudofunctor.DescentData.pullFunctor modulesPseudofunctor
      (f := fun i ↦ (g i).left) (f' := fun i ↦ baseChangeMap f (g i)) w).mapIso eN ≪≫
    eqToIso (cT.pullFunctor_obj_twist w _) ≪≫
    (cT.pull w).twistFunctor.mapIso
      ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso modulesPseudofunctor
        (f := fun i ↦ (g i).left) (f' := fun i ↦ baseChangeMap f (g i)) w).app _) ≪≫
    eqToIso (congrArg (fun c ↦ DescentCocycle.twist c _) (cX.pull_ofBaseChange hbij)) ≪≫
    eKD.symm
  obtain ⟨eNK⟩ := nonempty_iso_of_toDescentData_iso _ hgX
    (inferInstanceAs ((Modules.pullback (pullback.snd f T.hom)).obj N').IsQuasicoherent)
    (inferInstanceAs K.IsQuasicoherent) E
  refine ⟨Pic.mk N', ⟨?_⟩⟩
  exact (ρ_ A).symm ≪≫ whiskerLeftIso A (eB.symm ≪≫ β_ B _) ≪≫ (α_ A _ B).symm ≪≫
    β_ K B ≪≫ whiskerLeftIso B (eNK.symm ≪≫
      (Modules.pullback _).mapIso (fromSkeletonToSkeletonIso N').symm)

/-- **The sheaf condition for `Pic_{X/S,σ}` along an fpqc covering.** Assume that `f` has a
section `σ` and that `𝒪_T ⟶ f_{T,*} 𝒪_{X_T}` is an isomorphism for every `T` over `S`. Then
`Pic_{X/S,σ}` satisfies the sheaf condition for every family `{T i ⟶ T}` whose underlying
family of schemes is an fpqc covering.

Existence of the gluing is fpqc descent of the normalized descent datum
(`AlgebraicGeometry.normalizedDescentData`), as in
`AlgebraicGeometry.isSheaf_picardFunctorNormalized`; uniqueness follows from
`AlgebraicGeometry.exists_iso_tensorObj_of_pic_map_eq` and
`AlgebraicGeometry.picardFunctorNormalized_eq_of_iso_tensorObj`.

(blueprint: `sk-cor-picard-pic-sheaf`, `lem-pc-k-sheaf`) -/
theorem isSheafFor_ofArrows_picardFunctorNormalized (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom)))
    {T : Over S} {ι : Type*} {T' : ι → Over S} (g : ∀ i, T' i ⟶ T)
    (hR : Presieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (g i).left) ∈
      fpqcPrecoverage T.left) :
    Presieve.IsSheafFor (picardFunctorNormalized f σ hσ).toFunctor (.ofArrows T' g) := by
  have hsurj (Y : Over S) : Function.Surjective (pullback.snd f Y.hom).appTop :=
    have := hf Y
    surjective_appTop_of_isIso_pushforwardUnitMap _
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
    have hg := ofArrows_baseChangeMap_mem_fpqcTopology f g hR
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
    obtain ⟨N, ⟨e⟩⟩ := exists_iso_tensorObj_of_pic_map_eq f hf g hR t.1 t'.1
      fun i ↦ congrArg Subtype.val ((ht i).trans (ht' i).symm)
    exact picardFunctorNormalized_eq_of_iso_tensorObj f σ hσ t t' _ ((fromSkeleton _).obj N.val)
      (SheafOfModules.unit _) e
      ((ρ_ _).symm ≪≫ whiskerLeftIso _ (Modules.pullbackObjUnitIso _).symm)

/-- **The sheaf condition for `Pic_{X/S,σ}` along a faithfully flat quasi-compact morphism.**
Under the hypotheses of `AlgebraicGeometry.isSheafFor_ofArrows_picardFunctorNormalized`,
`Pic_{X/S,σ}` satisfies the sheaf condition for a single morphism `T' ⟶ T` over `S` which is
flat, surjective and quasi-compact.

(blueprint: `sk-cor-picard-pic-sheaf`) -/
theorem isSheafFor_singleton_picardFunctorNormalized (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom)))
    {T T' : Over S} (π : T' ⟶ T) [Flat π.left] [Surjective π.left] [QuasiCompact π.left] :
    Presieve.IsSheafFor (picardFunctorNormalized f σ hσ).toFunctor (.singleton π) := by
  rw [← Presieve.ofArrows_pUnit.{0}]
  refine isSheafFor_ofArrows_picardFunctorNormalized f σ hσ hf (fun _ ↦ π) ?_
  rw [Presieve.ofArrows_pUnit]
  exact π.left.singleton_mem_fpqcPrecoverage

end AlgebraicGeometry
