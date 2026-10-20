/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModels
import Sheaf.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModelsComparison
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.Paper.ProEtaleConstantModulePullbackEncoding
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-! # Finitely presented local constant models on the pro-etale site

Source: Stacks Project, Tags 09AJ and 093U.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

open Opposite

private noncomputable def fixedModelSchemeIso {X : Scheme.{u}}
    {B : Type (u + 1)} [CommRing B]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B)) (U : X.ProEt)
    (M : ModuleCat.{u + 1} B) :
    (F.over U ≅ (constantSheaf ((ProEt.topology X).over U) _).obj M) ≃
      ((ProEtale.upperStar (ModuleCat.{u + 1} B) U.hom).obj F ≅
        (constantSheaf (ProEt.topology U.left) _).obj M) := by
  have : (ProEt.sliceEquiv X U).inverse.IsDenseSubsite
      (ProEt.topology U.left) ((ProEt.topology X).over U) := ProEt.sliceDense X U
  let E := (ProEt.sliceEquiv X U).sheafCongr
    ((ProEt.topology X).over U) (ProEt.topology U.left) (ModuleCat.{u + 1} B)
  let r : E.functor.obj (F.over U) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} B) U.hom).obj F :=
    (ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))) ≪≫
      ((ProEtale.upperStarIsoLocalizationRestriction _ U.hom U.prop).app F).symm
  let c := ((ProEt.sliceEquiv X U).constantSheafSheafCongrIso
    ((ProEt.topology X).over U) (ProEt.topology U.left)
    (ModuleCat.{u + 1} B) (Over.mkIdTerminal (X := U))).app M
  exact
    { toFun := fun e ↦ r.symm ≪≫ E.functor.mapIso e ≪≫ c
      invFun := fun e ↦ E.functor.preimageIso (r ≪≫ e ≪≫ c.symm)
      left_inv := by intro e; apply Iso.ext; apply E.functor.map_injective; simp [r, c]
      right_inv := by intro e; apply Iso.ext; simp }

private noncomputable def fixedConstantPullbackIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (B : Type (u + 1)) [CommRing B] (M : ModuleCat.{u + 1} B) :
    (ProEtale.upperStar (ModuleCat.{u + 1} B) f).obj
        ((constantSheaf (ProEt.topology Y) _).obj M) ≅
      (constantSheaf (ProEt.topology X) _).obj M :=
  (Functor.isoWhiskerLeft (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} B))
    (Functor.sheafPullbackConstruction.sheafPullbackIso (proEtaleBaseChange f) _
      (ProEt.topology Y) (ProEt.topology X)).symm).app M ≪≫
    ((proEtaleBaseChange f).constantSheafsheafPullbackIso (ModuleCat.{u + 1} B)
      (ProEt.topology Y) (ProEt.topology X) (ProEt.isTerminalMkId Y)
      ((ProEt.isTerminalMkId Y).isTerminalObj (proEtaleBaseChange f) _)).app M

private theorem fixedModels_pullback {X Y : Scheme.{u}} (b : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B]
    (F : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} B))
    (hF : ProFiniteModels.fixedModels (ProEt.topology Y) B F) :
    ProFiniteModels.fixedModels (ProEt.topology X) B
      ((ProEtale.upperStar (ModuleCat.{u + 1} B) b).obj F) := by
  classical
  obtain ⟨T, hT, ht⟩ := hF (ProEt.mk (𝟙 Y))
  obtain ⟨R, hR, hRT⟩ := ProEt.mem_topology_iff.mp hT
  obtain ⟨I, U, a, rfl⟩ := R.exists_eq_ofArrows
  have ha (i : I) : (a i).left = (U i).hom := by
    have hw := MorphismProperty.Over.w (a i)
    change (a i).left ≫ 𝟙 Y = (U i).hom at hw
    change (a i).left = (U i).hom
    exact (Category.comp_id (a i).left).symm.trans hw
  have hg : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      proetalePrecoverage Y := by
    have h := ProEt.mem_precoverage_iff.mp hR
    simp only [Presieve.map_ofArrows, Functor.comp_obj, Functor.comp_map,
      ProEt.forget, MorphismProperty.Over.forget, MorphismProperty.Comma.forget,
      Over.forget, Comma.fst] at h
    change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (a i).left) ∈
      proetalePrecoverage Y at h
    simpa only [ha] using h
  have hm (i : I) : ∃ M : ModuleCat.{u + 1} B, Module.Finite B M ∧
      Nonempty ((ProEtale.upperStar (ModuleCat.{u + 1} B) (U i).hom).obj F ≅
        (constantSheaf (ProEt.topology (U i).left) _).obj M) := by
    obtain ⟨M, hM, ⟨e⟩⟩ := ht (U i) (a i) (hRT _ _ (Presieve.ofArrows.mk i))
    exact ⟨M, hM, ⟨fixedModelSchemeIso F (U i) M e⟩⟩
  intro V
  let g (i : I) := (U i).hom
  let q (i : I) : (U i).left ⟶ Y := g i
  have : ∀ i : I, WeaklyEtale (q i) := fun i ↦ (U i).prop
  let Z (i : I) : X.ProEt := ProEt.mk (pullback.snd (q i) b)
  let z (i : I) := (Z i).hom
  have hz : Presieve.ofArrows (fun i ↦ (Z i).left) z ∈ proetalePrecoverage X :=
    Precoverage.mem_coverings_of_isPullback q hg b z (fun i ↦ pullback.fst (q i) b)
      (fun i ↦ (IsPullback.of_hasPullback (q i) b).flip)
  let W (i : I) := ProEt.baseChange (z i) V
  let c (i : I) : W i ⟶ V := ProEt.baseChangeHom (z i) V
  refine ⟨Sieve.ofArrows W c, ProEt.ofArrows_baseChange_mem_topology V z hz,
    fun Q f hf ↦ ?_⟩
  obtain ⟨D, d, e, ⟨i⟩, rfl⟩ := hf
  obtain ⟨M, hM, ⟨em⟩⟩ := hm i
  refine ⟨M, hM, ⟨(fixedModelSchemeIso _ Q M).symm ?_⟩⟩
  let p : Q.left ⟶ (U i).left := d.left ≫ pullback.snd V.hom (z i) ≫
    pullback.fst (q i) b
  have hp : Q.hom ≫ b = p ≫ (U i).hom := by
    calc
      Q.hom ≫ b = (d.left ≫ (W i).hom) ≫ b :=
        congrArg (fun k ↦ k ≫ b) (MorphismProperty.Over.w d).symm
      _ = (d.left ≫ (pullback.snd V.hom (z i) ≫ z i)) ≫ b :=
        congrArg (fun k ↦ (d.left ≫ k) ≫ b) (pullback.condition (f := V.hom) (g := z i))
      _ = (d.left ≫ pullback.snd V.hom (z i)) ≫
          (pullback.snd (q i) b ≫ b) := by simp only [Category.assoc]; rfl
      _ = (d.left ≫ pullback.snd V.hom (z i)) ≫
          (pullback.fst (q i) b ≫ (U i).hom) :=
        congrArg (fun k ↦ (d.left ≫ pullback.snd V.hom (z i)) ≫ k)
          (pullback.condition (f := q i) (g := b)).symm
      _ = p ≫ (U i).hom := by simp only [p, Category.assoc]
  exact ((ProEtale.upperStarComp _ Q.hom b).app F).symm ≪≫
    eqToIso (congrArg (fun f ↦ (ProEtale.upperStar (ModuleCat.{u + 1} B) f).obj F) hp) ≪≫
    (ProEtale.upperStarComp _ p (U i).hom).app F ≪≫
    (ProEtale.upperStar _ p).mapIso em ≪≫ fixedConstantPullbackIso p B M

/-- Inverse image preserves finitely presented constant local models.
Source: Stacks Project, Tag 093R, lemma-pullback-locally-constant.
(blueprint: lem-sfb-proetale-fp-local-models-pullback).

Proof: pull a trivializing cover back along scheme base change, which preserves
coverings. Localization exchange identifies restriction of inverse image with inverse
image on the localized sites. Inverse image takes the constant module with value M to
that same constant module, compatibly with its constant scalar action, by the constant
sheaf universal property. Thus each original finitely presented value remains a local
model. Pull the resulting cover back to every test object; transitivity of covering
sieves yields the assertion. No geometric points or finiteness of R as a set is used. -/
theorem proEtale_fp_localModels_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y R))
    (hF : IsFinitelyPresentedLocallyConstantProEtaleModule F) :
    IsFinitelyPresentedLocallyConstantProEtaleModule
      (proEtaleConstantModulePullback f R F) := by
  apply (ProFiniteModels.intrinsic_fixedModels X R _).mpr
  have := constantComparison_isIso f R
  obtain ⟨e⟩ := proEtaleModuleRestriction_pullback_of_isIso f R F
  exact ProFiniteModels.fixedModels_of_iso (ProEt.topology X) (ULift.{u + 1, u} R) e.symm
    (fixedModels_pullback f (ULift.{u + 1, u} R) _
      ((ProFiniteModels.intrinsic_fixedModels Y R F).mp hF))

end AlgebraicGeometry.Scheme
