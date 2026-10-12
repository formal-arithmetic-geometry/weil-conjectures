/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition

import Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening
import Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp
import Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening

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

variable (Λ : Type (u + 1)) [CommRing Λ]

section Survival

variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- The property "the chosen cokernel element survives" of schemes `π : T' ⟶ T` over `T`.

Fix a Cartesian square `sq` with base `g : T ⟶ S`, a sheaf `F` on `T_ét`, a point `x` of `X`
and an element `ξ` of the stalk of `R^q h_* e⁻¹ F` at the geometric point over `x`. For
`π : T' ⟶ T` let `Y' = T' ×_S X`. The property holds for `π` if the image of `ξ` under the
transition map to the stalk of `R^q h'_* e'⁻¹ π⁻¹ F` is not in the image of the base-change
map of the square over `π ≫ g`. -/
def Etale.SurvivesBaseChange (q : ℤ) (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    ⦃T' : Scheme.{u}⦄ (π : T' ⟶ T) : Prop :=
  ((X.uliftPointSmallEtale x).sheafFiber.map
      (Etale.baseChangeTargetTransition Λ e h q π
        (sq.lift (pullback.fst (π ≫ g) p ≫ π) (pullback.snd (π ≫ g) p)
          (by rw [Category.assoc]; exact pullback.condition))
        (pullback.fst (π ≫ g) p) (pullback.snd (π ≫ g) p) (sq.lift_fst _ _ _)
        (sq.lift_snd _ _ _) F)).hom ξ ∉
    Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
      (Etale.baseChangeHomologyMap Λ (IsPullback.of_hasPullback (π ≫ g) p) q
        (((π)^*[ModuleCat.{u + 1} Λ]).obj F))).hom

variable {Λ}

/-- Along the identity of `T` the transition maps do not change the base-change map: an
element `ξ` not in the image of the base-change map over `T` survives along `𝟙 T`. -/
theorem Etale.survivesBaseChange_id (q : ℤ) (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    (hξ : ξ ∉ Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
      (Etale.baseChangeHomologyMap Λ sq q F)).hom) :
    Etale.SurvivesBaseChange Λ q sq F x ξ (𝟙 T) := by
  have hpb := IsPullback.of_hasPullback (𝟙 T ≫ g) p
  let a := sq.lift (pullback.fst (𝟙 T ≫ g) p ≫ 𝟙 T) (pullback.snd (𝟙 T ≫ g) p)
    (by rw [Category.assoc]; exact pullback.condition)
  have hc := Etale.baseChangeHomologyMap_comp_baseChangeTargetTransition Λ sq q (𝟙 T) hpb a
    (sq.lift_fst _ _ _) (sq.lift_snd _ _ _) F
  let b : Y ⟶ pullback (𝟙 T ≫ g) p :=
    pullback.lift e h (by rw [Category.id_comp]; exact sq.w)
  have hab : a ≫ b = 𝟙 _ := pullback.hom_ext (by simp [a, b]) (by simp [a, b])
  have hba : b ≫ a = 𝟙 _ := sq.hom_ext (by simp [a, b]) (by simp [a, b])
  have degT : CommSq a (pullback.snd (𝟙 T ≫ g) p) h (𝟙 X) :=
    ⟨by rw [sq.lift_snd, Category.comp_id]⟩
  have hT : IsIso (Etale.baseChangeTargetTransition Λ e h q (𝟙 T) a (pullback.fst (𝟙 T ≫ g) p)
      (pullback.snd (𝟙 T ≫ g) p) (sq.lift_fst _ _ _) (sq.lift_snd _ _ _) F) := by
    rw [Etale.baseChangeTargetTransition,
      Etale.lowerStarPlusTransition_eq_baseChange Λ a h _ (sq.lift_snd _ _ _) degT]
    have := fun K ↦ Etale.isIso_baseChange_app_of_inverses Λ degT b (𝟙 X) hab hba
      (Category.id_comp _) (Category.id_comp _) K
    infer_instance
  have degS : CommSq (𝟙 T) (𝟙 T ≫ g) g (𝟙 S) := ⟨by rw [Category.comp_id]⟩
  have hS : IsIso (Etale.baseChangeSourceTransition Λ p g q (𝟙 T) F) := by
    rw [Etale.baseChangeSourceTransition,
      Etale.lowerStarPlusTransition_eq_baseChange Λ (𝟙 T) g _ rfl degS]
    have := fun K ↦ Etale.isIso_baseChange_app_of_inverses Λ degS (𝟙 T) (𝟙 S)
      (Category.id_comp _) (Category.id_comp _) (Category.id_comp _) (Category.id_comp _) K
    infer_instance
  rintro ⟨η', hη'⟩
  apply hξ
  have hc' := congrArg (fun f ↦ ModuleCat.Hom.hom ((X.uliftPointSmallEtale x).sheafFiber.map f)) hc
  simp only [Functor.map_comp, ModuleCat.hom_comp] at hc'
  refine ⟨(inv ((X.uliftPointSmallEtale x).sheafFiber.map
    (Etale.baseChangeSourceTransition Λ p g q (𝟙 T) F))).hom η', ?_⟩
  apply ((ConcreteCategory.isIso_iff_bijective ((X.uliftPointSmallEtale x).sheafFiber.map
    (Etale.baseChangeTargetTransition Λ e h q (𝟙 T) a (pullback.fst (𝟙 T ≫ g) p)
      (pullback.snd (𝟙 T ≫ g) p) (sq.lift_fst _ _ _) (sq.lift_snd _ _ _) F))).1
        inferInstance).1
  have h1 := LinearMap.congr_fun hc' ((inv ((X.uliftPointSmallEtale x).sheafFiber.map
    (Etale.baseChangeSourceTransition Λ p g q (𝟙 T) F))).hom η')
  simp only [LinearMap.coe_comp, Function.comp_apply] at h1
  rw [← hη']
  convert h1 using 2
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, IsIso.inv_hom_id, ModuleCat.hom_id,
    LinearMap.id_apply]

private lemma baseChangeHomologyMap_range_congr
    {X S T Y : Scheme.{u}} {p : X ⟶ S} {g₁ g₂ : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    (hg : g₁ = g₂) (sq₁ : IsPullback e h g₁ p) (sq₂ : IsPullback e h g₂ p)
    (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X) :
    Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
      (Etale.baseChangeHomologyMap Λ sq₁ q F)).hom =
    Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
      (Etale.baseChangeHomologyMap Λ sq₂ q F)).hom := by
  subst hg
  rfl

/-- Step (1) of blueprint `sbc-lem-bc-failure-field`: the survival of `ξ` is invariant under
thickenings. A thickening does not change the étale site (blueprint
`sbc-lem-thickening-etale-site`, `AlgebraicGeometry.Etale.isEquivalence_upperStar_of_thickening`),
so the transition maps along it are isomorphisms compatible with the base-change maps. -/
theorem Etale.survivesBaseChange_comp_iff_of_surjective (q : ℤ) (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    {T₁ T₂ : Scheme.{u}} (i : T₁ ⟶ T₂) [IsClosedImmersion i] (hi : Function.Surjective i.base)
    (f₂ : T₂ ⟶ T) :
    Etale.SurvivesBaseChange Λ q sq F x ξ (i ≫ f₂) ↔ Etale.SurvivesBaseChange Λ q sq F x ξ f₂ := by
  let e₂ := pullback.fst (f₂ ≫ g) p
  let h₂ := pullback.snd (f₂ ≫ g) p
  let e₁ := pullback.fst ((i ≫ f₂) ≫ g) p
  let h₁ := pullback.snd ((i ≫ f₂) ≫ g) p
  have sq₂ : IsPullback e₂ h₂ (f₂ ≫ g) p := IsPullback.of_hasPullback _ _
  have sq₁ : IsPullback e₁ h₁ (i ≫ (f₂ ≫ g)) p := by
    have hs : IsPullback e₁ h₁ ((i ≫ f₂) ≫ g) p := IsPullback.of_hasPullback _ _
    exact Eq.mp (congrArg (fun k ↦ IsPullback e₁ h₁ k p) (Category.assoc i f₂ g)) hs
  let a₂ := sq.lift (e₂ ≫ f₂) h₂ (by rw [Category.assoc]; exact sq₂.w)
  let a₁ := sq₂.lift (e₁ ≫ i) h₁ ((Category.assoc e₁ i (f₂ ≫ g)).trans sq₁.w)
  have wa₂ : a₂ ≫ e = e₂ ≫ f₂ := sq.lift_fst _ _ _
  have wh₂ : a₂ ≫ h = h₂ := sq.lift_snd _ _ _
  have wa₁ : a₁ ≫ e₂ = e₁ ≫ i := sq₂.lift_fst _ _ _
  have wh₁ : a₁ ≫ h₂ = h₁ := sq₂.lift_snd _ _ _
  have sqa : IsPullback a₁ e₁ e₂ i :=
    (wh₁.symm ▸ sq₁.flip).of_right wa₁ sq₂.flip
  let ν := (Etale.upperStarComp (ModuleCat.{u + 1} Λ) i f₂ (i ≫ f₂) rfl).inv.app F
  let t₂ := Etale.baseChangeTargetTransition Λ e h q f₂ a₂ e₂ h₂ wa₂ wh₂ F
  let v := Etale.baseChangeTargetTransition Λ e₂ h₂ q i a₁ e₁ h₁ wa₁ wh₁
      (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F) ≫
    (Etale.baseChangeTargetFunctor Λ e₁ h₁ q).map ν
  let u' := Etale.baseChangeSourceTransition Λ p (f₂ ≫ g) q i
      (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F) ≫
    (Etale.baseChangeSourceFunctor Λ p (i ≫ (f₂ ≫ g)) q).map ν
  let b₂ := Etale.baseChangeHomologyMap Λ sq₂ q (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F)
  let b₁ := Etale.baseChangeHomologyMap Λ sq₁ q (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F)
  have hv : IsIso v := by
    have := Etale.baseChangeTargetTransition_isIso_of_thickening Λ e₂ h₂ q i hi
      a₁ e₁ h₁ sqa wh₁ (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F)
    dsimp [v, ν]
    infer_instance
  have hu : IsIso u' := by
    have := Etale.baseChangeSourceTransition_isIso_of_thickening Λ p (f₂ ≫ g) q i hi
      (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F)
    dsimp [u', ν]
    infer_instance
  have hb : b₂ ≫ v = u' ≫ b₁ := by
    have hc := Etale.baseChangeHomologyMap_comp_baseChangeTargetTransition Λ sq₂ q i
      sq₁ a₁ wa₁ wh₁ (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F)
    have hn := Etale.baseChangeHomologyMap_naturality Λ sq₁ q ν
    have hc' := congrArg (fun k ↦ k ≫ (Etale.baseChangeTargetFunctor Λ e₁ h₁ q).map ν) hc
    have hn' := congrArg (fun k ↦ Etale.baseChangeSourceTransition Λ p (f₂ ≫ g) q i
      (((f₂)^*[ModuleCat.{u + 1} Λ]).obj F) ≫ k) hn
    exact (Category.assoc _ _ _).symm.trans
      (hc'.trans ((Category.assoc _ _ _).trans
        (hn'.trans (Category.assoc _ _ _).symm)))
  have ht := Etale.baseChangeTargetTransition_comp Λ e h q f₂ a₂ e₂ h₂ wa₂ wh₂
    i a₁ e₁ h₁ wa₁ wh₁ F
  have w₁ : (e₁ ≫ (i ≫ f₂)) ≫ g = h₁ ≫ p :=
    (Category.assoc e₁ (i ≫ f₂) g).trans
      ((congrArg (fun k ↦ e₁ ≫ k) (Category.assoc i f₂ g)).trans sq₁.w)
  have ha : a₁ ≫ a₂ = sq.lift (e₁ ≫ (i ≫ f₂)) h₁ w₁ := by
    apply sq.hom_ext
    · exact ((Category.assoc a₁ a₂ e).trans (congrArg (fun k ↦ a₁ ≫ k) wa₂)).trans
        ((Category.assoc a₁ e₂ f₂).symm.trans
          ((congrArg (fun k ↦ k ≫ f₂) wa₁).trans
            ((Category.assoc e₁ i f₂).trans (sq.lift_fst _ _ _).symm)))
    · simp only [Category.assoc, wh₂, wh₁, sq.lift_snd]
  simp only [ha] at ht
  change t₂ ≫ v = _ at ht
  have hc := congrArg (fun f ↦ ModuleCat.Hom.hom
    ((X.uliftPointSmallEtale x).sheafFiber.map f)) hb
  simp only [Functor.map_comp, ModuleCat.hom_comp] at hc
  have ht' := congrArg (fun f ↦ ModuleCat.Hom.hom
    ((X.uliftPointSmallEtale x).sheafFiber.map f)) ht
  simp only [Functor.map_comp, ModuleCat.hom_comp] at ht'
  have hv' := (ConcreteCategory.isIso_iff_bijective
    ((X.uliftPointSmallEtale x).sheafFiber.map v)).1 inferInstance
  have hu' := (ConcreteCategory.isIso_iff_bijective
    ((X.uliftPointSmallEtale x).sheafFiber.map u')).1 inferInstance
  unfold Etale.SurvivesBaseChange
  rw [← ht']
  rw [baseChangeHomologyMap_range_congr (Λ := Λ) (Category.assoc i f₂ g)
    (IsPullback.of_hasPullback ((i ≫ f₂) ≫ g) p) sq₁ q
    (((i ≫ f₂)^*[ModuleCat.{u + 1} Λ]).obj F) x]
  change (((X.uliftPointSmallEtale x).sheafFiber.map v).hom ∘ₗ
      ((X.uliftPointSmallEtale x).sheafFiber.map t₂).hom) ξ ∉
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map b₁).hom ↔
    ((X.uliftPointSmallEtale x).sheafFiber.map t₂).hom ξ ∉
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map b₂).hom
  simp only [LinearMap.comp_apply]
  constructor
  · intro h₁' h₂'
    obtain ⟨η, hη⟩ := h₂'
    apply h₁'
    refine ⟨((X.uliftPointSmallEtale x).sheafFiber.map u').hom η, ?_⟩
    have hcη := LinearMap.congr_fun hc η
    simpa only [LinearMap.coe_comp, Function.comp_apply, hη] using hcη.symm
  · intro h₂' h₁'
    obtain ⟨η₁, hη₁⟩ := h₁'
    obtain ⟨η₂, hη₂⟩ := hu'.2 η₁
    apply h₂'
    refine ⟨η₂, hv'.1 ?_⟩
    have hcη := LinearMap.congr_fun hc η₂
    simpa only [LinearMap.coe_comp, Function.comp_apply, hη₂, hη₁] using hcη


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
    Etale.SurvivesBaseChange Λ q sq F x ξ c.pt.hom :=
  sorry

/-- Step (3) of blueprint `sbc-lem-bc-failure-field`: if `ξ` survives over a quasi-compact
quasi-separated `T'` and `Z ⊆ T'` is closed with quasi-compact complement `V`, then `ξ`
survives over `V` or over `Z`. Embed `π⁻¹ F` into `j_* J ⊕ i_* i⁻¹ π⁻¹ F` with `J` injective
on `V`; by `AlgebraicGeometry.Etale.mono_cokernelMap` the image of `ξ` survives in one of the
summands. For the closed summand use the exactness of `i_*`; for the open summand use the
universal base-change property in degrees `< q` for the base change of `p` along `T' ⟶ S`,
the Leray spectral sequence, and `AlgebraicGeometry.Etale.mono_cokernelDesc`. -/
theorem Etale.survivesBaseChange_or_of_isClosedImmersion [IsAffine S] (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q') (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    {T' Z : Scheme.{u}} [CompactSpace T'] [QuasiSeparatedSpace T'] (f : T' ⟶ T)
    (V : T'.Opens) (hV : IsCompact (V : Set T')) (i : Z ⟶ T') [IsClosedImmersion i]
    (hi : Set.range i.base = (V : Set T')ᶜ) (hf : Etale.SurvivesBaseChange Λ q sq F x ξ f) :
    Etale.SurvivesBaseChange Λ q sq F x ξ (V.ι ≫ f) ∨
      Etale.SurvivesBaseChange Λ q sq F x ξ (i ≫ f) :=
  sorry

/-- Step (4) of blueprint `sbc-lem-bc-failure-field`: nothing survives over the empty scheme,
since there the fibre `T' ×_S X` is empty and `R^q h'_* e'⁻¹ π⁻¹ F` vanishes. -/
theorem Etale.not_survivesBaseChange_of_isEmpty (q : ℤ) (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ))
    {T' : Scheme.{u}} (π : T' ⟶ T) [IsEmpty T'] :
    ¬ Etale.SurvivesBaseChange Λ q sq F x ξ π := by
  intro hP
  apply hP
  have : IsEmpty ↥(pullback (π ≫ g) p) :=
    ⟨fun y ↦ isEmptyElim ((pullback.fst (π ≫ g) p).base y)⟩
  have hsheaf (G : Sheaf (pullback (π ≫ g) p).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      IsZero G := by
    refine (IsZero.iff_id_eq_zero G).2 (IsTerminal.hom_ext ?_ _ _)
    refine IsTerminal.isTerminalOfObj (sheafToPresheaf _ _) _ (Functor.isTerminal fun U ↦ ?_)
    have : IsEmpty U.unop.left :=
      ⟨fun y ↦ isEmptyElim (show ↥(pullback (π ≫ g) p) from U.unop.hom.base y)⟩
    exact Scheme.Etale.isTerminalSectionsOfIsEmpty G U.unop
  have hK (K : DerivedCategory.Plus
      (Sheaf (pullback (π ≫ g) p).smallEtaleTopology (ModuleCat.{u + 1} Λ))) : IsZero K :=
    IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι K
      (DerivedCategory.isZero_of_forall_isZero_homology _ fun _ ↦ hsheaf _)
  have : R+((pullback.snd (π ≫ g) p)_*[ModuleCat.{u + 1} Λ]).IsRightAdjoint :=
    (Etale.derivedUpperStarLowerStarAdjunctionPlus _ _).isRightAdjoint
  have hzero : IsZero ((Etale.baseChangeTargetFunctor Λ (pullback.fst (π ≫ g) p)
      (pullback.snd (π ≫ g) p) q).obj (((π)^*[ModuleCat.{u + 1} Λ]).obj F)) :=
    (DerivedCategory.Plus.homologyFunctor _ q).map_isZero
      (R+((pullback.snd (π ≫ g) p)_*[ModuleCat.{u + 1} Λ]).map_isZero (hK _))
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u}
  have : ((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).IsLeftAdjoint :=
    inferInstance
  have := (ModuleCat.isZero_iff_subsingleton.1
    (((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).map_isZero hzero))
  exact ⟨0, Subsingleton.elim _ _⟩

/-- The property "the chosen cokernel element survives" satisfies the hypotheses of the
minimal-counterexample lemma `AlgebraicGeometry.exists_spec_field_of_isQcqsLocalProperty`. -/
theorem Etale.isQcqsLocalProperty_survivesBaseChange [IsAffine S] (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q') (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    (ξ : ((X.uliftPointSmallEtale x).sheafFiber.obj
      ((Etale.baseChangeTargetFunctor Λ e h q).obj F) : ModuleCat.{u + 1} Λ)) :
    T.IsQcqsLocalProperty (Etale.SurvivesBaseChange Λ q sq F x ξ) where
  invariant_under_thickening i _ hi f₂ :=
    Etale.survivesBaseChange_comp_iff_of_surjective q sq F x ξ i hi f₂
  compatible_with_cofilteredLimit D _ _ _ c hc hD :=
    Etale.survivesBaseChange_of_isLimit q sq F x ξ D c hc hD
  of_opens_or_closedComplement f V hV i _ hi hf :=
    Etale.survivesBaseChange_or_of_isClosedImmersion q hq hprev sq F x ξ f V hV i hi hf
  not_of_isEmpty π _ :=
    Etale.not_survivesBaseChange_of_isEmpty q sq F x ξ π

end Survival

end AlgebraicGeometry
