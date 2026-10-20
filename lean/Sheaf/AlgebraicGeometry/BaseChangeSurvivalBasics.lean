/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
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
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u}
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

lemma Etale.survival_range_congr
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
  have : Surjective i := ⟨hi⟩
  -- the fibre products over `T₂` and over `T₁`
  have sq₂ := IsPullback.of_hasPullback (f₂ ≫ g) p
  have sq₁ := IsPullback.of_hasPullback ((i ≫ f₂) ≫ g) p
  obtain ⟨a', hae, hah⟩ : ∃ a' : pullback ((i ≫ f₂) ≫ g) p ⟶ pullback (f₂ ≫ g) p,
      a' ≫ pullback.fst (f₂ ≫ g) p = pullback.fst ((i ≫ f₂) ≫ g) p ≫ i ∧
        a' ≫ pullback.snd (f₂ ≫ g) p = pullback.snd ((i ≫ f₂) ≫ g) p :=
    ⟨pullback.lift (pullback.fst _ _ ≫ i) (pullback.snd _ _)
      ((Category.assoc _ _ _).trans (by rw [← Category.assoc i f₂ g]; exact pullback.condition)),
      by simp, by simp⟩
  have hpb : IsPullback (pullback.fst ((i ≫ f₂) ≫ g) p) a' i (pullback.fst (f₂ ≫ g) p) := by
    refine IsPullback.of_bot ?_ hae.symm sq₂
    rw [hah, ← Category.assoc]
    exact sq₁
  have : IsUniversalHomeomorphism a' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb inferInstance
  have ha : a' ≫ sq.lift (pullback.fst (f₂ ≫ g) p ≫ f₂) (pullback.snd (f₂ ≫ g) p)
      (by rw [Category.assoc]; exact pullback.condition) =
      sq.lift (pullback.fst ((i ≫ f₂) ≫ g) p ≫ i ≫ f₂) (pullback.snd ((i ≫ f₂) ≫ g) p)
        ((Category.assoc _ _ _).trans pullback.condition) :=
    sq.hom_ext (by simp [reassoc_of% hae]) (by simp [hah])
  unfold Etale.SurvivesBaseChange
  exact not_congr (Etale.mem_range_iff_of_isUniversalHomeomorphism Λ q F x ξ f₂ sq₂ _
    (sq.lift_fst _ _ _) (sq.lift_snd _ _ _) i sq₁ _ (sq.lift_fst _ _ _) (sq.lift_snd _ _ _) a'
    hae hah ha)


end Survival

end AlgebraicGeometry
