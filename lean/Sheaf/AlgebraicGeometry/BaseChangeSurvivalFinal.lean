/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeSurvivalClosedOpen
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
