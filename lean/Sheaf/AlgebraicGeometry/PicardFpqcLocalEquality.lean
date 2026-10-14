/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Defs

/-! # Fpqc-local equality of relative Picard classes

Source: Stacks Project, Tags 0D28, 0D2B and 023T.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

open Scheme

/-- If the structure sheaf has universally trivial direct image, two invertible modules
whose classes agree fpqc-locally have the same relative Picard class.

Proof: form their tensor quotient, which is locally trivial on an fpqc covering.
The ratio cocycle between its canonical descent datum and that of the pulled-back unit
comes from the base, since global sections commute with every base change. Descend the
corresponding twisted unit module on the base by fpqc module descent. Fully faithful
module descent identifies its pullback with the tensor quotient. Thus the original modules
differ by a pullback from the base, which is precisely equality in the relative Picard sheaf.
Source: Stacks Project, Tags 0D28, 0D2B and 023T; the ratio-cocycle argument is also the
proof of `exists_iso_tensorObj_of_toPicardFunctor_app_eq` in `Picard.Defs`.
(blueprint: lem-pd-picard-fpqc-local-equality) -/
theorem toPicardFunctor_app_eq_of_fpqc_equalizer {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (pullback.snd f T.hom)))
    {T : Over S} (L L' : (picardPresheaf f).obj (op T))
    (hR : Presheaf.equalizerSieve (F := picardPresheaf f) L L' ∈ (fpqcTopology.over S) T) :
    (toPicardFunctor f).app (op T) L = (toPicardFunctor f).app (op T) L' := by
  apply (toPicardFunctor_app_eq_iff f hf L L').2
  have hbij (Y : Over S) : Function.Bijective (pullback.snd f Y.hom).appTop :=
    have := hf Y
    bijective_appTop_of_isIso_pushforwardUnitMap _
  rw [GrothendieckTopology.mem_over_iff,
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hR
  obtain ⟨R, hR, hle⟩ := hR
  obtain ⟨ι, Z, a, rfl⟩ := R.exists_eq_ofArrows
  let T' (i : ι) : Over S := Over.mk (a i ≫ T.hom)
  let g (i : ι) : T' i ⟶ T := Over.homMk (a i)
  have heq (i : ι) : Pic.map (baseChangeMap f (g i)) L =
      Pic.map (baseChangeMap f (g i)) L' :=
    (Sieve.overEquiv_iff _ _).1 (hle _ _ (Presieve.ofArrows.mk i))
  have hgT : Sieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (g i).left) ∈
      fpqcTopology T.left := Precoverage.generate_mem_toGrothendieck hR
  have hgX : Sieve.ofArrows _ (fun i ↦ baseChangeMap f (g i)) ∈
      fpqcTopology (pullback f T.hom) :=
    Precoverage.generate_mem_toGrothendieck
      (Precoverage.mem_coverings_of_isPullback (fun i ↦ (g i).left) hR
        (pullback.snd f T.hom) (fun i ↦ baseChangeMap f (g i))
        (fun i ↦ pullback.snd f (T' i).hom)
        (fun i ↦ isPullback_baseChangeMap f (g i)))
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
    ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso modulesPseudofunctor w).app
      N).symm ≪≫
    (Pseudofunctor.DescentData.pullFunctor modulesPseudofunctor w).mapIso eN ≪≫
    eqToIso (cT.pullFunctor_obj_twist w _) ≪≫
    (cT.pull w).twistFunctor.mapIso
      ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso modulesPseudofunctor w).app _) ≪≫
    eqToIso (congrArg (fun c ↦ DescentCocycle.twist c _) (cX.pull_ofBaseChange hbij)) ≪≫
    eKD.symm
  obtain ⟨eNK⟩ := nonempty_iso_of_toDescentData_iso _ hgX
    (inferInstanceAs ((Modules.pullback (pullback.snd f T.hom)).obj N').IsQuasicoherent)
    (inferInstanceAs K.IsQuasicoherent) E
  refine ⟨Pic.mk N', ⟨?_⟩⟩
  exact (ρ_ A).symm ≪≫ whiskerLeftIso A (eB.symm ≪≫ β_ B _) ≪≫ (α_ A _ B).symm ≪≫
    β_ K B ≪≫ whiskerLeftIso B (eNK.symm ≪≫
      (Modules.pullback _).mapIso (fromSkeletonToSkeletonIso N').symm)

end AlgebraicGeometry
