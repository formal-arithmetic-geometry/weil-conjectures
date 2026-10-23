/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundleSum
public import WeilConjectures.EtaleCohomology.Purity.Smooth.LocalizedChern
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct

/-!
# The Thom class of a direct sum, and the Whitney product of localized top Chern classes

For vector bundles `π : V ⟶ S` of rank `d` and `ρ : X ⟶ S` of rank `e`, the Thom class of the
direct sum `V ⊕ X = V ×_S X` (`AlgebraicGeometry.VectorBundle.sum`) is the cup product with
supports of the pullbacks of the Thom classes of `V` and `X`
(`AlgebraicGeometry.VectorBundle.thomClass_sum`). Consequently the localized top Chern class of
a section `(s, t)` of `V ⊕ X` is the cup product of those of `s` and `t`
(`AlgebraicGeometry.VectorBundle.localizedTopChern_sum`, (L3) of `thm-pur-localized-top-chern`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

namespace VectorBundle

variable {V X S : Scheme.{u}} {d e : ℕ} {π : V ⟶ S} {ρ : X ⟶ S} (E : VectorBundle d π)
  (F : VectorBundle e ρ)

/-- The zero section of the direct sum is the intersection of the pullbacks of the zero sections
of the summands. -/
lemma isPullback_sumZero :
    IsPullback (pullback.lift (𝟙 S) (E.sumZero F) (by simp))
      (pullback.lift (𝟙 S) (E.sumZero F) (by simp))
      (pullback.snd E.zero (pullback.fst π ρ)) (pullback.snd F.zero (pullback.snd π ρ)) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ s.fst ≫ pullback.fst E.zero (pullback.fst π ρ)) ?_ ?_ ?_⟩⟩ <;> intro s
  all_goals
    have e₁ : s.fst ≫ pullback.fst E.zero (pullback.fst π ρ) =
        (s.fst ≫ pullback.snd E.zero (pullback.fst π ρ)) ≫ pullback.fst π ρ ≫ π := by
      rw [Category.assoc, ← pullback.condition_assoc, E.zero_comp, Category.comp_id]
    have e₂ : s.snd ≫ pullback.fst F.zero (pullback.snd π ρ) =
        (s.snd ≫ pullback.snd F.zero (pullback.snd π ρ)) ≫ pullback.snd π ρ ≫ ρ := by
      rw [Category.assoc, ← pullback.condition_assoc, F.zero_comp, Category.comp_id]
    have ht : s.fst ≫ pullback.fst E.zero (pullback.fst π ρ) =
        s.snd ≫ pullback.fst F.zero (pullback.snd π ρ) := by
      rw [e₁, e₂, s.condition, pullback.condition]
    have hx : (s.fst ≫ pullback.fst E.zero (pullback.fst π ρ)) ≫ E.sumZero F =
        s.fst ≫ pullback.snd E.zero (pullback.fst π ρ) := by
      apply pullback.hom_ext
      · rw [Category.assoc, sumZero_fst, Category.assoc, Category.assoc, pullback.condition]
      · rw [Category.assoc, sumZero_snd, ht, Category.assoc, pullback.condition]
        simp [s.condition]
  · apply pullback.hom_ext
    · simp
    · simpa using hx
  · apply pullback.hom_ext
    · simpa using ht
    · simpa [s.condition] using hx
  · intro m h₁ _
    rw [← h₁, Category.assoc, pullback.lift_fst, Category.comp_id]
/-- The coordinates of the direct sum: those of `V` followed by those of `X`. -/
lemma sum_coord (p : E.ι × F.ι) :
    (E.sum F).coord p = Fin.append
      (fun a ↦ (fstRes (π := π) (ρ := ρ) (E.sumU F p) (E.U p.1) inf_le_left).appTop
        (E.coord p.1 a))
      (fun b ↦ (sndRes (π := π) (ρ := ρ) (E.sumU F p) (F.U p.2) inf_le_right).appTop
        (F.coord p.2 b)) := by
  funext k
  induction k using Fin.addCases with
  | left a =>
    rw [Fin.append_left]
    exact E.sumChart_hom_appTop_coord_castAdd F p a
  | right b =>
    rw [Fin.append_right]
    exact E.sumChart_hom_appTop_coord_natAdd F p b
/-! ### The Thom class of a direct sum -/

section Thom

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ V] [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ (pullback π ρ)]
  {k : Type u} [Field k] (aS : S ⟶ Spec (.of k)) [IsSeparated aS] [LocallyOfFiniteType aS]

attribute [local instance] HasInvertibleExponent.opens

/-- The pullback to `V ⊕ X` of the Thom class of `V`, supported on `0 ⊕ X`. -/
noncomputable def thomClassLeft : constantComplex Λ (pullback π ρ) ⟶
    (R(pullback.snd E.zero (pullback.fst π ρ))_![ModuleCat.{u + 1} Λ]).obj
      ((R(pullback.snd E.zero (pullback.fst π ρ))^![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ (pullback π ρ) d)⟦2 * (d : ℤ)⟧)) :=
  restrictSupportedClass (ModuleCat.{u + 1} Λ) (pullback.fst π ρ) E.zero _
    (pullback.fst E.zero (pullback.fst π ρ)) (IsPullback.of_hasPullback _ _)
    (leftDerivedUpperStarConstantComplexIso Λ _).inv (leftDerivedUpperStarTateShiftIso Λ _ d)
    (E.thomClass Λ aS)

/-- The pullback to `V ⊕ X` of the Thom class of `X`, supported on `V ⊕ 0`. -/
noncomputable def thomClassRight : constantComplex Λ (pullback π ρ) ⟶
    (R(pullback.snd F.zero (pullback.snd π ρ))_![ModuleCat.{u + 1} Λ]).obj
      ((R(pullback.snd F.zero (pullback.snd π ρ))^![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ (pullback π ρ) e)⟦2 * (e : ℤ)⟧)) :=
  restrictSupportedClass (ModuleCat.{u + 1} Λ) (pullback.snd π ρ) F.zero _
    (pullback.fst F.zero (pullback.snd π ρ)) (IsPullback.of_hasPullback _ _)
    (leftDerivedUpperStarConstantComplexIso Λ _).inv (leftDerivedUpperStarTateShiftIso Λ _ e)
    (F.thomClass Λ aS)

lemma range_sumZero :
    Set.range (E.sum F).zero.base =
      Set.range (pullback.snd E.zero (pullback.fst π ρ)).base ∩
        Set.range (pullback.snd F.zero (pullback.snd π ρ)).base :=
  Scheme.range_eq_inter_of_isPullback (E.isPullback_sumZero F) (pullback.lift_snd _ _ _)

include aS in
/-- Blueprint `def-pur-vector-bundle-thom-class`: the Thom class of a direct sum `V ⊕ X` is the
cup product with supports of the pullbacks of the Thom classes of `V` and `X`. On a chart, the
coordinates of `V ⊕ X` are those of `V` followed by those of `X`, and the product of the Kummer
boundaries of a concatenation is the cup product of the products
(`AlgebraicGeometry.Etale.kummerBoundaryProduct_append`). -/
theorem thomClass_sum :
    (E.sum F).thomClass Λ aS =
      cupWithSupportsTateObject Λ (pullback.snd E.zero (pullback.fst π ρ))
          (pullback.snd F.zero (pullback.snd π ρ)) (E.sum F).zero (E.range_sumZero F)
          (E.thomClassLeft (ρ := ρ) Λ aS) (F.thomClassRight (π := π) Λ aS) ≫
        eqToHom (by rfl) := by
  refine ((E.sum F).eq_thomClass_of_frameRestriction Λ aS fun p ↦ ?_).symm
  have : HasInvertibleExponent Λ (π ⁻¹ᵁ E.U p.1).toScheme := .of_hom (π ⁻¹ᵁ E.U p.1).ι
  have : HasInvertibleExponent Λ (ρ ⁻¹ᵁ F.U p.2).toScheme := .of_hom (ρ ⁻¹ᵁ F.U p.2).ι
  let U := sumπ (π := π) (ρ := ρ) ⁻¹ᵁ E.sumU F p
  let a₁ := fstRes (π := π) (ρ := ρ) (E.sumU F p) (E.U p.1) inf_le_left
  let a₂ := sndRes (π := π) (ρ := ρ) (E.sumU F p) (F.U p.2) inf_le_right
  let f₁ : Fin d → Γ(U.toScheme, ⊤) := fun t ↦ a₁.appTop (E.coord p.1 t)
  let f₂ : Fin e → Γ(U.toScheme, ⊤) := fun t ↦ a₂.appTop (F.coord p.2 t)
  obtain ⟨g₁, hg₁⟩ : ∃ g, IsPullback g (U.toScheme.zeroLocusSubschemeι (Set.range f₁))
      ((E.frame p.1).U.zeroLocusSubschemeι (Set.range (E.frame p.1).f)) a₁ :=
    ⟨_, isPullback_zeroLocusSubschemeι a₁ _ _ (by rw [← Set.range_comp]; rfl)⟩
  obtain ⟨g₂, hg₂⟩ : ∃ g, IsPullback g (U.toScheme.zeroLocusSubschemeι (Set.range f₂))
      ((F.frame p.2).U.zeroLocusSubschemeι (Set.range (F.frame p.2).f)) a₂ :=
    ⟨_, isPullback_zeroLocusSubschemeι a₂ _ _ (by rw [← Set.range_comp]; rfl)⟩
  have hp₁ : IsPullback (g₁ ≫ (E.frame p.1).toZ) (U.toScheme.zeroLocusSubschemeι (Set.range f₁))
      E.zero (U.ι ≫ pullback.fst π ρ) := by
    have := hg₁.paste_horiz (E.frame p.1).isPullback
    rwa [frame_e, fstRes_ι] at this
  have hp₂ : IsPullback (g₂ ≫ (F.frame p.2).toZ) (U.toScheme.zeroLocusSubschemeι (Set.range f₂))
      F.zero (U.ι ≫ pullback.snd π ρ) := by
    have := hg₂.paste_horiz (F.frame p.2).isPullback
    rwa [frame_e, sndRes_ι] at this
  let gL := (IsPullback.of_hasPullback E.zero (pullback.fst π ρ)).lift (g₁ ≫ (E.frame p.1).toZ)
    (U.toScheme.zeroLocusSubschemeι (Set.range f₁) ≫ U.ι) (by simpa using hp₁.w)
  let gR := (IsPullback.of_hasPullback F.zero (pullback.snd π ρ)).lift (g₂ ≫ (F.frame p.2).toZ)
    (U.toScheme.zeroLocusSubschemeι (Set.range f₂) ≫ U.ι) (by simpa using hp₂.w)
  have hpL : IsPullback gL (U.toScheme.zeroLocusSubschemeι (Set.range f₁))
      (pullback.snd E.zero (pullback.fst π ρ)) U.ι :=
    IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hp₁) (IsPullback.lift_snd _ _ _ _)
      (IsPullback.of_hasPullback E.zero (pullback.fst π ρ))
  have hpR : IsPullback gR (U.toScheme.zeroLocusSubschemeι (Set.range f₂))
      (pullback.snd F.zero (pullback.snd π ρ)) U.ι :=
    IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hp₂) (IsPullback.lift_snd _ _ _ _)
      (IsPullback.of_hasPullback F.zero (pullback.snd π ρ))
  have e₁ : restrictSupportedClass (ModuleCat.{u + 1} Λ) U.ι _ _ gL hpL
      (leftDerivedUpperStarConstantComplexIso Λ U.ι).inv
      (leftDerivedUpperStarTateShiftIso Λ U.ι d) (E.thomClassLeft (ρ := ρ) Λ aS) =
        kummerBoundaryProduct Λ f₁ := by
    have hout := hpL.paste_horiz (IsPullback.of_hasPullback E.zero (pullback.fst π ρ))
    rw [thomClassLeft, ← restrictSupportedClass_comp_tateShift Λ U.ι (pullback.fst π ρ) _ rfl
      E.zero _ _ _ (IsPullback.of_hasPullback E.zero (pullback.fst π ρ)) gL hpL _ hout,
      restrictSupportedClass_comp_tateShift Λ a₁ (E.frame p.1).e _ (fstRes_ι _ _ _).symm E.zero
        _ _ (E.frame p.1).toZ (E.frame p.1).isPullback g₁ hg₁ _ hout]
    have h := E.frameRestriction_thomClass Λ aS p.1
    rw [frameRestriction] at h
    rw [h]
    exact restrictSupportedClass_kummerBoundaryProduct Λ a₁ (E.frame p.1).f f₁ (fun _ ↦ rfl) g₁ hg₁
  have e₂ : restrictSupportedClass (ModuleCat.{u + 1} Λ) U.ι _ _ gR hpR
      (leftDerivedUpperStarConstantComplexIso Λ U.ι).inv
      (leftDerivedUpperStarTateShiftIso Λ U.ι e) (F.thomClassRight (π := π) Λ aS) =
        kummerBoundaryProduct Λ f₂ := by
    have hout := hpR.paste_horiz (IsPullback.of_hasPullback F.zero (pullback.snd π ρ))
    rw [thomClassRight, ← restrictSupportedClass_comp_tateShift Λ U.ι (pullback.snd π ρ) _ rfl
      F.zero _ _ _ (IsPullback.of_hasPullback F.zero (pullback.snd π ρ)) gR hpR _ hout,
      restrictSupportedClass_comp_tateShift Λ a₂ (F.frame p.2).e _ (sndRes_ι _ _ _).symm F.zero
        _ _ (F.frame p.2).toZ (F.frame p.2).isPullback g₂ hg₂ _ hout]
    have h := F.frameRestriction_thomClass Λ aS p.2
    rw [frameRestriction] at h
    rw [h]
    exact restrictSupportedClass_kummerBoundaryProduct Λ a₂ (F.frame p.2).f f₂ (fun _ ↦ rfl) g₂ hg₂
  have key : ∀ (c : Fin (d + e) → Γ(U.toScheme, ⊤)) (_ : c = Fin.append f₁ f₂)
      (gG : U.toScheme.zeroLocusSubscheme (Set.range c) ⟶ S)
      (hgG : IsPullback gG (U.toScheme.zeroLocusSubschemeι (Set.range c)) (E.sum F).zero U.ι),
      restrictSupportedClass (ModuleCat.{u + 1} Λ) U.ι _ _ gG hgG
          (leftDerivedUpperStarConstantComplexIso Λ U.ι).inv
          (leftDerivedUpperStarTateShiftIso Λ U.ι (d + e : ℕ))
          (cupWithSupportsTateObject Λ (pullback.snd E.zero (pullback.fst π ρ))
            (pullback.snd F.zero (pullback.snd π ρ)) (E.sum F).zero (E.range_sumZero F)
            (E.thomClassLeft (ρ := ρ) Λ aS) (F.thomClassRight (π := π) Λ aS) ≫
            eqToHom (by push_cast; rfl)) =
        kummerBoundaryProduct Λ c := by
    rintro _ rfl gG hgG
    rw [restrictSupportedClass_comp_eqToHom Λ U.ι _ _ _ _ (by push_cast; rfl),
      restrictSupportedClass_cupWithSupportsTateObject Λ U.ι _ _ (E.sum F).zero
        (U.toScheme.zeroLocusSubschemeι (Set.range f₁))
        (U.toScheme.zeroLocusSubschemeι (Set.range f₂)) _ _
        (by rw [Fin.range_append, Scheme.range_zeroLocusSubschemeι_union]) gL gR gG hpL hpR hgG,
      e₁, e₂]
    exact (kummerBoundaryProduct_append Λ f₁ f₂).symm
  exact key _ (E.sum_coord F p) _ _
/-! ### The Whitney product of localized top Chern classes -/

variable {s : S ⟶ V} {t : S ⟶ X} (hs : s ≫ π = 𝟙 S) (ht : t ≫ ρ = 𝟙 S)

/-- The section `(s, t)` of the direct sum. -/
noncomputable def sumSection : S ⟶ pullback π ρ :=
  pullback.lift s t (by rw [hs, ht])

lemma range_sumSection_zero :
    Set.range (pullback.snd (E.sum F).zero (sumSection hs ht)).base =
      Set.range (pullback.snd E.zero s).base ∩ Set.range (pullback.snd F.zero t).base := by
  rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, Scheme.Pullback.range_snd,
    E.range_sumZero F, Set.preimage_inter, Scheme.Pullback.range_snd,
    Scheme.Pullback.range_snd, ← Set.preimage_comp, ← Set.preimage_comp]
  have h₁ : (⇑(pullback.fst π ρ) ∘ ⇑(sumSection hs ht)) = ⇑s := by
    funext x
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, sumSection, pullback.lift_fst]
  have h₂ : (⇑(pullback.snd π ρ) ∘ ⇑(sumSection hs ht)) = ⇑t := by
    funext x
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, sumSection, pullback.lift_snd]
  rw [h₁, h₂]

lemma isPullback_sumSection_left :
    IsPullback (pullback.lift (pullback.fst E.zero s)
        (pullback.snd E.zero s ≫ sumSection hs ht) (by simp [sumSection]))
      (pullback.snd E.zero s) (pullback.snd E.zero (pullback.fst π ρ)) (sumSection hs ht) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback E.zero (pullback.fst π ρ))
  rw [pullback.lift_fst, sumSection, pullback.lift_fst]
  exact IsPullback.of_hasPullback E.zero s

lemma isPullback_sumSection_right :
    IsPullback (pullback.lift (pullback.fst F.zero t)
        (pullback.snd F.zero t ≫ sumSection hs ht) (by simp [sumSection]))
      (pullback.snd F.zero t) (pullback.snd F.zero (pullback.snd π ρ)) (sumSection hs ht) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback F.zero (pullback.snd π ρ))
  rw [pullback.lift_fst, sumSection, pullback.lift_snd]
  exact IsPullback.of_hasPullback F.zero t

include aS in
/-- Blueprint `thm-pur-localized-top-chern`: Localized top Chern class

*(L3), direct sums.* For sections `s` of `V` and `t` of `X`, the localized top Chern class of the
section `(s, t)` of the direct sum `V ⊕ X` is the cup product with supports of the localized top
Chern classes of `s` and `t`, supported on `Z(s, t) = Z(s) ∩ Z(t)`: the Thom class of `V ⊕ X` is
the cup product of those of the summands
(`AlgebraicGeometry.VectorBundle.thomClass_sum`), and restriction of supports commutes with cup
products. -/
theorem localizedTopChern_sum :
    haveI : HasInvertibleExponent Λ S := .of_hom E.zero
    (E.sum F).localizedTopChern (sumSection hs ht) Λ aS =
      cupWithSupportsTateObject Λ (pullback.snd E.zero s) (pullback.snd F.zero t)
          (pullback.snd (E.sum F).zero (sumSection hs ht)) (E.range_sumSection_zero F hs ht)
          (E.localizedTopChern s Λ aS) (F.localizedTopChern t Λ aS) ≫
        eqToHom (by rfl) := by
  have : HasInvertibleExponent Λ S := .of_hom E.zero
  rw [localizedTopChern, thomClass_sum,
    restrictSupportedClass_comp_eqToHom Λ _ _ _ _ _ (by push_cast; rfl),
    restrictSupportedClass_cupWithSupportsTateObject Λ (sumSection hs ht) _ _ _ _ _ _ _
      (E.range_sumSection_zero F hs ht) _ _ _ (E.isPullback_sumSection_left hs ht)
      (F.isPullback_sumSection_right hs ht) (IsPullback.of_hasPullback _ _)]
  congr 2
  · rw [thomClassLeft, ← restrictSupportedClass_comp_tateShift Λ (sumSection hs ht)
      (pullback.fst π ρ) s (by rw [sumSection, pullback.lift_fst]) E.zero _ _ _
      (IsPullback.of_hasPullback _ _) _ (E.isPullback_sumSection_left hs ht) _
      (IsPullback.of_hasPullback E.zero s)]
    rfl
  · rw [thomClassRight, ← restrictSupportedClass_comp_tateShift Λ (sumSection hs ht)
      (pullback.snd π ρ) t (by rw [sumSection, pullback.lift_snd]) F.zero _ _ _
      (IsPullback.of_hasPullback _ _) _ (F.isPullback_sumSection_right hs ht) _
      (IsPullback.of_hasPullback F.zero t)]
    rfl

end Thom

end VectorBundle

end AlgebraicGeometry
