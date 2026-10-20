/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeSurvivalBasics
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.ClosedOpen
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Limit
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Colimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.EpiMono


import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.CriticalMap
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero

/-!
# Survival of a cokernel element under base change

An element `ξ` of a geometric stalk of `R^q h_* e⁻¹ F` that is not in the image of the
base-change map is transported along `π : T' ⟶ T` by the transition maps
`AlgebraicGeometry.Etale.baseChangeTargetTransition`; the property
`AlgebraicGeometry.Etale.SurvivesBaseChange` asks that its image is still not in the image of
the base-change map over `T'`. This file verifies the four hypotheses of the
minimal-counterexample lemma `AlgebraicGeometry.exists_spec_field_of_isQcqsLocalProperty` for
it: invariance under thickenings, compatibility with limits, the closed–open splitting and the
failure over the empty scheme.

## Main definitions

- `AlgebraicGeometry.Etale.SurvivesBaseChange`: the property "the chosen cokernel element
  survives" of schemes over `T`.

## Main statements

- `AlgebraicGeometry.Etale.isQcqsLocalProperty_survivesBaseChange`: that property satisfies
  the hypotheses of the minimal-counterexample lemma.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable {Λ : Type (u + 1)} [CommRing Λ]

section Survival

variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

set_option maxHeartbeats 400000 in
-- the transition maps are compared through large terms of the derived categories
/-- Step (2) of blueprint `sbc-lem-bc-failure-field`: the survival of `ξ` passes to cofiltered
limits along affine transition morphisms. By the limit theorem for higher direct images
(blueprint `sbc-lem-higher-direct-image-limit`,
`AlgebraicGeometry.Etale.higherDirectImage_limit`) the stalks over the limit are the colimits
of the stalks over the stages, on both sides of the base-change map. -/
theorem Etale.survivesBaseChange_of_isLimit [IsAffine S] (q : ℤ) (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over T)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    (c : Cone D) (hc : IsLimit ((Over.forget T).mapCone c))
    (hD : ∀ i, Etale.SurvivesBaseChange Λ q sq F x ξ (D.obj i).hom) :
    Etale.SurvivesBaseChange Λ q sq F x ξ c.pt.hom := by
  have hlf (U : Over T) :
      ((Etale.stageFunctor sq).obj U).hom ≫ e = pullback.fst (U.hom ≫ g) p ≫ U.hom :=
    sq.lift_fst _ _ _
  have hls (U : Over T) : ((Etale.stageFunctor sq).obj U).hom ≫ h = pullback.snd (U.hom ≫ g) p :=
    sq.lift_snd _ _ _
  have sqU (U : Over T) : IsPullback (pullback.fst (U.hom ≫ g) p)
      (((Etale.stageFunctor sq).obj U).hom ≫ h) (U.hom ≫ g) p := by
    rw [hls]; exact IsPullback.of_hasPullback _ _
  have hconv (U : Over T) : Etale.SurvivesBaseChange Λ q sq F x ξ U.hom ↔
      ((X.uliftPointSmallEtale x).sheafFiber.map ((DerivedCategory.Plus.homologyFunctor _ q).map
        (Etale.targetTransitionPlus Λ e h U.hom ((Etale.stageFunctor sq).obj U).hom
          (pullback.fst (U.hom ≫ g) p) (((Etale.stageFunctor sq).obj U).hom ≫ h) (hlf U) rfl
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))).hom ξ ∉
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
        ((DerivedCategory.Plus.homologyFunctor _ q).map
          ((Etale.baseChange (ModuleCat.{u + 1} Λ) (sqU U).toCommSq).app
            (D+((U.hom)^*[ModuleCat.{u + 1} Λ]).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))).hom := by
    rw [← Etale.mem_range_baseChangeHomologyMap_iff Λ q F x ξ U.hom _ _ (sqU U) _ (hlf U) rfl]
    exact not_congr (Etale.mem_range_baseChangeHomologyMap_congr Λ q F x ξ U.hom _ _ _ _ _ _
      (hlf U) (hls U) rfl)
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((D ⋙ Over.forget T).map f) :=
    fun f ↦ (inferInstance : IsAffineHom (D.map f).left)
  have : ∀ i, CompactSpace ((D ⋙ Over.forget T).obj i) :=
    fun i ↦ (inferInstance : CompactSpace (D.obj i).left)
  have i₀ : I := IsCofiltered.nonempty.some
  have : IsAffineHom (c.π.app i₀).left :=
    isAffineHom_π_app (D ⋙ Over.forget T) ((Over.forget T).mapCone c) hc i₀
  have : CompactSpace c.pt.left :=
    Scheme.compactSpace_of_isLimit (D ⋙ Over.forget T) ((Over.forget T).mapCone c) hc
  have : QuasiSeparatedSpace c.pt.left := quasiSeparatedSpace_of_quasiSeparated (c.π.app i₀).left
  have hw (U V : Over T) (φ : U ⟶ V) : ((Etale.stageFunctor sq).map φ).left ≫
      pullback.fst (V.hom ≫ g) p = pullback.fst (U.hom ≫ g) p ≫ φ.left := by simp
  have hwh (U V : Over T) (φ : U ⟶ V) : ((Etale.stageFunctor sq).map φ).left ≫
      ((Etale.stageFunctor sq).obj V).hom ≫ h = ((Etale.stageFunctor sq).obj U).hom ≫ h := by
    rw [← Category.assoc, Over.w]
  rw [hconv]
  refine ModuleCat.notMem_range_of_forall_notMem_range
    (A := fun i ↦ (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).obj
      (D+((p)^*[ModuleCat.{u + 1} Λ]).obj (R+(((D.obj i).hom ≫ g)_*[ModuleCat.{u + 1} Λ]).obj
        (D+(((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj 
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))))
    (B := fun i ↦ (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).obj
      (R+((((Etale.stageFunctor sq).obj (D.obj i)).hom ≫ h)_*[ModuleCat.{u + 1} Λ]).obj
        (D+((pullback.fst ((D.obj i).hom ≫ g) p)^*[ModuleCat.{u + 1} Λ]).obj
          (D+(((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj 
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))))
    (φ := fun i ↦ (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) (sqU (D.obj i)).toCommSq).app
        (D+(((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj 
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))
    (tA := fun {i j} f ↦ (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).map
      (D+((p)^*[ModuleCat.{u + 1} Λ]).map (Etale.overLowerStarTransition Λ g (D.obj i).hom
        (D.obj j).hom (D.map f).left (Over.w (D.map f))
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))
    (tB := fun {i j} f ↦ (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).map
      (Etale.overTargetTransition Λ _ _ _ _ (D.obj i).hom (D.obj j).hom (D.map f).left
        ((Etale.stageFunctor sq).map (D.map f)).left (hw _ _ (D.map f)) (hwh _ _ (D.map f))
        (Over.w (D.map f)) ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (sA := fun i ↦ (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).map
      (D+((p)^*[ModuleCat.{u + 1} Λ]).map (Etale.overLowerStarTransition Λ g (D.obj i).hom c.pt.hom
        (c.π.app i).left (Over.w (c.π.app i)) ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))
    (sB := fun i ↦ (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).map
      (Etale.overTargetTransition Λ (pullback.fst ((D.obj i).hom ≫ g) p)
        (((Etale.stageFunctor sq).obj (D.obj i)).hom ≫ h) (pullback.fst (c.pt.hom ≫ g) p)
        (((Etale.stageFunctor sq).obj c.pt).hom ≫ h) (D.obj i).hom c.pt.hom (c.π.app i).left
        ((Etale.stageFunctor sq).map (c.π.app i)).left (hw c.pt (D.obj i) (c.π.app i))
        (hwh c.pt (D.obj i) (c.π.app i))
        (Over.w (c.π.app i)) ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (τ := fun i ↦ (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).map
      (Etale.targetTransitionPlus Λ e h (D.obj i).hom ((Etale.stageFunctor sq).obj (D.obj i)).hom
        (pullback.fst ((D.obj i).hom ≫ g) p) (((Etale.stageFunctor sq).obj (D.obj i)).hom ≫ h)
        (hlf (D.obj i)) rfl ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (Al := (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).obj
      (D+((p)^*[ModuleCat.{u + 1} Λ]).obj (R+((c.pt.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).obj
        (D+((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj 
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))))
    (Bl := (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).obj
      (R+((((Etale.stageFunctor sq).obj c.pt).hom ≫ h)_*[ModuleCat.{u + 1} Λ]).obj
        (D+((pullback.fst (c.pt.hom ≫ g) p)^*[ModuleCat.{u + 1} Λ]).obj
          (D+((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj 
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))))
    (φl := (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) (sqU c.pt).toCommSq).app
        (D+((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj 
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))
    (τl := (DerivedCategory.Plus.homologyFunctor _ q ⋙
        (X.uliftPointSmallEtale x).sheafFiber).map
      (Etale.targetTransitionPlus Λ e h c.pt.hom ((Etale.stageFunctor sq).obj c.pt).hom
        (pullback.fst (c.pt.hom ≫ g) p) (((Etale.stageFunctor sq).obj c.pt).hom ≫ h)
        (hlf c.pt) rfl ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (hτ := ?_) (hτl := ?_) (hφ := ?_) (hφl := ?_) (hsA := ?_) (hA := ?_) (hB := ?_)
    (hξ := fun i ↦ (hconv (D.obj i)).1 (hD i))
  case refine_1 =>
    intro i j f
    rw [← Functor.map_comp, Etale.targetTransitionPlus_comp_overTargetTransition Λ e h
      _ _ _ _ _ _ _ _ (hlf _) rfl (hlf _) rfl _ _ _ _ _
      (Over.w ((Etale.stageFunctor sq).map (D.map f)))]
  case refine_2 =>
    intro i
    rw [← Functor.map_comp]
    exact congrArg _ (Etale.targetTransitionPlus_comp_overTargetTransition Λ e h
      (pullback.fst ((D.obj i).hom ≫ g) p) (((Etale.stageFunctor sq).obj (D.obj i)).hom ≫ h)
      (pullback.fst (c.pt.hom ≫ g) p) (((Etale.stageFunctor sq).obj c.pt).hom ≫ h) (D.obj i).hom
      c.pt.hom _ _ (hlf _) rfl (hlf c.pt) rfl (c.π.app i).left
      ((Etale.stageFunctor sq).map (c.π.app i)).left (hw c.pt (D.obj i) (c.π.app i))
      (hwh c.pt (D.obj i) (c.π.app i)) (Over.w (c.π.app i))
      (Over.w ((Etale.stageFunctor sq).map (c.π.app i))) _)
  case refine_3 =>
    intro i j f
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (Etale.baseChange_app_comp_overTargetTransition Λ g
      (sqU (D.obj i)).toCommSq (sqU (D.obj j)).toCommSq _ _ (hw _ _ (D.map f)) (hwh _ _ (D.map f))
      (Over.w (D.map f)) _)
  case refine_4 =>
    intro i
    exact (Functor.map_comp _ _ _).symm.trans ((congrArg _
      (Etale.baseChange_app_comp_overTargetTransition Λ g
      (sqU (D.obj i)).toCommSq (sqU c.pt).toCommSq _ _ (hw c.pt (D.obj i) (c.π.app i))
      (hwh c.pt (D.obj i) (c.π.app i)) (Over.w (c.π.app i)) _)).trans (Functor.map_comp _ _ _))
  case refine_5 =>
    intro i j f
    exact (Functor.map_comp _ _ _).symm.trans (congrArg _ ((Functor.map_comp _ _ _).symm.trans
      (congrArg _ (Etale.overLowerStarTransition_comp Λ g (D.obj i).hom (D.obj j).hom c.pt.hom
        (D.map f).left (c.π.app j).left (c.π.app i).left (Over.w (D.map f)) (Over.w (c.π.app j))
        (Over.w (c.π.app i)) (by rw [← Over.comp_left, c.w f]) _))))
  case refine_6 =>
    have lim := Etale.higherDirectImage_limit Λ g F D c hc q
    intro y
    refine ModuleCat.mem_iSup_range_of_comm _
      (fun i ↦ (X.uliftPointSmallEtale x).sheafFiber.map (((p)^*[ModuleCat.{u + 1} Λ]).map
        (Etale.higherDirectImageOverMap Λ g F q (c.π.app i))))
      (fun i ↦ (X.uliftPointSmallEtale x).sheafFiber.map
        (Etale.sourceStageIso Λ p g F q (D.obj i)).hom)
      ((X.uliftPointSmallEtale x).sheafFiber.mapIso (Etale.sourceStageIso Λ p g F q c.pt))
      (fun i ↦ ?_) y
      (Etale.mem_iSup_range_sheafFiber_map_upperStar Λ p x _ _ (fun s y ↦ (lim s).1 y) _)
    exact Etale.sheafFiber_map_sourceStageIso_naturality Λ p g F q (c.π.app i) x
  case refine_7 =>
    have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((D ⋙ Etale.stageFunctor sq).map f).left :=
      fun f ↦ (inferInstance : IsAffineHom ((Etale.stageFunctor sq).map (D.map f)).left)
    have : ∀ i, QuasiCompact (((D ⋙ Etale.stageFunctor sq).obj i).hom ≫ h) := fun i ↦ by
      change QuasiCompact (((Etale.stageFunctor sq).obj (D.obj i)).hom ≫ h)
      rw [hls]; infer_instance
    have : ∀ i, QuasiSeparated (((D ⋙ Etale.stageFunctor sq).obj i).hom ≫ h) := fun i ↦ by
      change QuasiSeparated (((Etale.stageFunctor sq).obj (D.obj i)).hom ≫ h)
      rw [hls]; infer_instance
    have : QuasiCompact (((Etale.stageFunctor sq).mapCone c).pt.hom ≫ h) := by
      change QuasiCompact (((Etale.stageFunctor sq).obj c.pt).hom ≫ h)
      rw [hls]; infer_instance
    have : QuasiSeparated (((Etale.stageFunctor sq).mapCone c).pt.hom ≫ h) := by
      change QuasiSeparated (((Etale.stageFunctor sq).obj c.pt).hom ≫ h)
      rw [hls]; infer_instance
    have lim := Etale.higherDirectImage_limit Λ h (((e)^*[ModuleCat.{u + 1} Λ]).obj F)
      (D ⋙ Etale.stageFunctor sq) ((Etale.stageFunctor sq).mapCone c)
      (Etale.isLimitStageFunctorMapCone sq c hc) q x
    intro i b hb
    have h₁ := congrArg (fun m ↦ m.hom b)
      (Etale.sheafFiber_map_stageTargetTransition Λ sq F q x (U := c.pt) (c.π.app i))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁
    obtain ⟨j, f, hf⟩ := lim.2 i _ (h₁.symm.trans ((congrArg _ hb).trans (map_zero _)))
    refine ⟨j, f, ?_⟩
    have h₂ := congrArg (fun m ↦ m.hom b)
      (Etale.sheafFiber_map_stageTargetTransition Λ sq F q x (D.map f))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₂
    exact (injective_iff_map_eq_zero _).1
      ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1 _ (h₂.trans hf)



end Survival

end AlgebraicGeometry
