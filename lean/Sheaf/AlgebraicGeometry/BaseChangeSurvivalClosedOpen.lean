/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeSurvivalLimit
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.ClosedOpen
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Limit
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Colimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.EpiMono


import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.CriticalMap
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero

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
      Etale.SurvivesBaseChange Λ q sq F x ξ (i ≫ f) := by
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u}
  have : PreservesFiniteLimits ((X.uliftPointSmallEtale x).sheafFiber
    (A := ModuleCat.{u + 1} Λ)) := inferInstance
  have : PreservesFiniteColimits ((X.uliftPointSmallEtale x).sheafFiber
    (A := ModuleCat.{u + 1} Λ)) := inferInstance
  have : ((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
    Functor.additive_of_preserves_binary_products _
  -- quasi-compactness and quasi-separatedness
  have : QuasiCompact (f ≫ g) := (quasiCompact_iff_compactSpace _).2 inferInstance
  have : QuasiSeparated (f ≫ g) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)).2 inferInstance
  have : CompactSpace V := isCompact_iff_compactSpace.1 hV
  have : QuasiCompact V.ι := (quasiCompact_iff_compactSpace _).2 inferInstance
  have hrange : Set.range i.base = (Set.range V.ι.base)ᶜ := by
    rw [hi]
    congr
    exact (Scheme.Opens.range_ι V).symm
  -- the base-change properties in lower degrees
  have hprev' : Etale.BaseChangeProperty Λ p (q - 1) :=
    (hprev (q - 1) (by lia)).baseChangeProperty
  have sq₂ := IsPullback.of_hasPullback (f ≫ g) p
  have hbc : ∀ a < q, Etale.BaseChangeProperty Λ (pullback.fst (f ≫ g) p) a :=
    fun a ha ↦ hprev a ha _ _ _ sq₂.flip
  have : (Etale.baseChangeTargetFunctor Λ (pullback.fst (f ≫ g) p) (pullback.snd (f ≫ g) p)
      q).Additive := by
    unfold Etale.baseChangeTargetFunctor
    infer_instance
  -- the fibre products over `V` and over `Z`
  have sqV : IsPullback (pullback.fst ((V.ι ≫ f) ≫ g) p)
      (pullback.lift (pullback.fst ((V.ι ≫ f) ≫ g) p ≫ V.ι) (pullback.snd ((V.ι ≫ f) ≫ g) p)
        (by simpa using (pullback.condition :
          pullback.fst ((V.ι ≫ f) ≫ g) p ≫ (V.ι ≫ f) ≫ g = _))) V.ι
      (pullback.fst (f ≫ g) p) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback (f ≫ g) p)
    rw [pullback.lift_snd, ← Category.assoc]
    exact IsPullback.of_hasPullback _ _
  have sqZ : IsPullback (pullback.fst ((i ≫ f) ≫ g) p)
      (pullback.lift (pullback.fst ((i ≫ f) ≫ g) p ≫ i) (pullback.snd ((i ≫ f) ≫ g) p)
        (by simpa using (pullback.condition :
          pullback.fst ((i ≫ f) ≫ g) p ≫ (i ≫ f) ≫ g = _))) i
      (pullback.fst (f ≫ g) p) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback (f ≫ g) p)
    rw [pullback.lift_snd, ← Category.assoc]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨βV, hβViso, hβV⟩ := Etale.exists_baseChangeTargetTransition_comp_eq Λ q F f
    (sq.lift (pullback.fst (f ≫ g) p ≫ f) (pullback.snd (f ≫ g) p)
      (by rw [Category.assoc]; exact pullback.condition)) (sq.lift_fst _ _ _) (sq.lift_snd _ _ _)
    V.ι (sq.lift (pullback.fst ((V.ι ≫ f) ≫ g) p ≫ V.ι ≫ f) (pullback.snd ((V.ι ≫ f) ≫ g) p)
      ((Category.assoc _ _ _).trans pullback.condition)) (sq.lift_fst _ _ _) (sq.lift_snd _ _ _)
    _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (sq.hom_ext (by simp) (by simp)) sqV.toCommSq
  obtain ⟨βZ, hβZiso, hβZ⟩ := Etale.exists_baseChangeTargetTransition_comp_eq Λ q F f
    (sq.lift (pullback.fst (f ≫ g) p ≫ f) (pullback.snd (f ≫ g) p)
      (by rw [Category.assoc]; exact pullback.condition)) (sq.lift_fst _ _ _) (sq.lift_snd _ _ _)
    i (sq.lift (pullback.fst ((i ≫ f) ≫ g) p ≫ i ≫ f) (pullback.snd ((i ≫ f) ≫ g) p)
      ((Category.assoc _ _ _).trans pullback.condition)) (sq.lift_fst _ _ _) (sq.lift_snd _ _ _)
    _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (sq.hom_ext (by simp) (by simp)) sqZ.toCommSq
  -- an injective sheaf on `V` containing `(V.ι ≫ f)^* F`
  obtain ⟨J, ι, _, _⟩ : ∃ (J : Sheaf V.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (ι : ((V.ι ≫ f)^*[ModuleCat.{u + 1} Λ]).obj F ⟶ J), Injective J ∧ Mono ι :=
    ⟨_, Injective.ι _, inferInstance, inferInstance⟩
  have hα₁ : ((V.ι)^*[ModuleCat.{u + 1} Λ]).map (βV ≫ ((V.ι)_*[ModuleCat.{u + 1} Λ]).map ι) ≫
      (Etale.upperStarLowerStarAdjunction _ V.ι).counit.app J =
      (((V.ι)^*[ModuleCat.{u + 1} Λ]).map βV ≫
        (Etale.upperStarLowerStarAdjunction _ V.ι).counit.app
          (((V.ι ≫ f)^*[ModuleCat.{u + 1} Λ]).obj F)) ≫ ι := by
    rw [Functor.map_comp, Category.assoc]
    erw [(Etale.upperStarLowerStarAdjunction _ V.ι).counit.naturality ι]
    rw [Category.assoc]
    rfl
  have : Mono (((V.ι)^*[ModuleCat.{u + 1} Λ]).map (βV ≫ ((V.ι)_*[ModuleCat.{u + 1} Λ]).map ι) ≫
      (Etale.upperStarLowerStarAdjunction _ V.ι).counit.app J) := by
    have := hβViso
    rw [hα₁]
    infer_instance
  have := hβZiso
  have hα := Etale.mono_biprod_lift Λ V.ι i hrange (βV ≫ ((V.ι)_*[ModuleCat.{u + 1} Λ]).map ι) βZ
  have hcok := Etale.mono_cokernelMap Λ q hq hprev' (IsPullback.of_hasPullback (f ≫ g) p)
    (biprod.lift (βV ≫ ((V.ι)_*[ModuleCat.{u + 1} Λ]).map ι) βZ)
  unfold Etale.SurvivesBaseChange at hf ⊢
  have key := fun y ↦ mem_range_of_mono_cokernelMap
    ((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ))
    (Etale.baseChangeHomologyMap Λ (IsPullback.of_hasPullback (f ≫ g) p) q
      (((f)^*[ModuleCat.{u + 1} Λ]).obj F))
    (Etale.baseChangeHomologyMap Λ (IsPullback.of_hasPullback (f ≫ g) p) q _)
    ((Etale.baseChangeSourceFunctor Λ p (f ≫ g) q).map
      (biprod.lift (βV ≫ ((V.ι)_*[ModuleCat.{u + 1} Λ]).map ι) βZ))
    ((Etale.baseChangeTargetFunctor Λ (pullback.fst (f ≫ g) p) (pullback.snd (f ≫ g) p) q).map
      (biprod.lift (βV ≫ ((V.ι)_*[ModuleCat.{u + 1} Λ]).map ι) βZ))
    (Etale.baseChangeHomologyMap_naturality Λ _ q _) y
  have hη := fun hmem ↦ hf (key _ hmem)
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨hVin, hZin⟩ := hcon
  rw [← hβV, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply] at hVin
  rw [← hβZ, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply] at hZin
  apply hη
  refine mem_range_of_decomp ((X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ))
    (fun G ↦ Etale.baseChangeHomologyMap Λ (IsPullback.of_hasPullback (f ≫ g) p) q G)
    (Etale.baseChangeHomologyMap_naturality Λ _ q) biprod.fst biprod.snd
    biprod.inl biprod.inr biprod.total _ ?_ ?_
  · by_contra hA
    refine Etale.notMem_range_of_baseChangeProperty Λ (IsPullback.of_hasPullback (f ≫ g) p)
      V.ι ((V.ι ≫ f) ≫ g) (IsPullback.of_hasPullback _ _) _ (pullback.lift_snd _ _ _) sqV q hq
      hbc βV ι x _ ?_ hVin
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp, biprod.lift_fst] at hA
    exact hA
  · by_contra hB
    refine Etale.notMem_range_of_isFinite Λ (IsPullback.of_hasPullback (f ≫ g) p)
      i ((i ≫ f) ≫ g) (Category.assoc _ _ _).symm (IsPullback.of_hasPullback _ _) _
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) sqZ q βZ x _ ?_ hZin
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp, biprod.lift_snd] at hB
    exact hB


end Survival

end AlgebraicGeometry
