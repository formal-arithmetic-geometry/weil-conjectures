/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic

/-! # Descent of stagewise additive bijections to pair-category Hom groups

In the pair category of a stage system, a family of additive bijections between the Hom
groups at all sufficiently large stages, compatible with the transports, descends to a unique
additive bijection between the Hom groups of the pair category.

## Main statements

* `CategoryTheory.StageSystem.PairCategory.homAddEquiv_descent`: the descended bijection.
* `CategoryTheory.StageSystem.PairCategory.homAddEquiv_descent_comp`: compatibility of
  descended bijections with precomposition.
-/

@[expose] public section

namespace CategoryTheory.StageSystem.PairCategory

variable {I : Type*} [Preorder I] [IsDirectedOrder I] {C : I → Type*} [∀ i, Category (C i)]
  [∀ i, Preadditive (C i)] {S : StageSystem C} [instP : Preadditive S.PairCategory]

/-- A family of additive bijections between the stage Hom groups of `L ⟶ H` and `T ⟶ N`,
compatible with the transports, descends to an additive bijection between the Hom groups
of the pair category, given on representatives by the stagewise bijections. -/
theorem homAddEquiv_descent
    (hadd : ∀ {X Y : S.PairCategory} {n : I} (hX : X.stage ≤ n) (hY : Y.stage ≤ n)
      (u v : X.toStage hX ⟶ Y.toStage hY),
        mkHom n hX hY u + mkHom n hX hY v = mkHom n hX hY (u + v))
    {L H T N : S.PairCategory}
    (Ψ : ∀ (F : I) (hL : L.stage ≤ F) (hH : H.stage ≤ F) (hT : T.stage ≤ F)
      (hN : N.stage ≤ F),
      (L.toStage hL ⟶ H.toStage hH) ≃+ (T.toStage hT ⟶ N.toStage hN))
    (htr : ∀ (F F' : I) (k : F ≤ F') (hL : L.stage ≤ F) (hH : H.stage ≤ F)
      (hT : T.stage ≤ F) (hN : N.stage ≤ F) (φ : L.toStage hL ⟶ H.toStage hH),
      S.tr k (Ψ F hL hH hT hN φ) =
        Ψ F' (hL.trans k) (hH.trans k) (hT.trans k) (hN.trans k) (S.tr k φ)) :
    ∃ σ : (L ⟶ H) ≃+ (T ⟶ N), ∀ (F : I) (hL : L.stage ≤ F) (hH : H.stage ≤ F)
      (hT : T.stage ≤ F) (hN : N.stage ≤ F) (φ : L.toStage hL ⟶ H.toStage hH),
      σ (mkHom F hL hH φ) = mkHom F hT hN (Ψ F hL hH hT hN φ) := by
  -- Every arrow is represented at a stage above the stages of `T` and `N`.
  have hrep (q : L ⟶ H) : ∃ (F : I) (hL : L.stage ≤ F) (hH : H.stage ≤ F)
      (hT : T.stage ≤ F) (hN : N.stage ≤ F) (φ : L.toStage hL ⟶ H.toStage hH),
      q = mkHom F hL hH φ := by
    obtain ⟨m, hTm, hNm⟩ := exists_ge_ge T.stage N.stage
    obtain ⟨F, hmF, hL, hH, φ, rfl⟩ := exists_le_mkHom_eq q m
    exact ⟨F, hL, hH, hTm.trans hmF, hNm.trans hmF, φ, rfl⟩
  -- The value on a representative does not depend on the representative.
  have hind (F F' : I) (hL : L.stage ≤ F) (hH : H.stage ≤ F) (hT : T.stage ≤ F)
      (hN : N.stage ≤ F) (hL' : L.stage ≤ F') (hH' : H.stage ≤ F') (hT' : T.stage ≤ F')
      (hN' : N.stage ≤ F') (φ : L.toStage hL ⟶ H.toStage hH)
      (φ' : L.toStage hL' ⟶ H.toStage hH') (e : mkHom F hL hH φ = mkHom F' hL' hH' φ') :
      mkHom F hT hN (Ψ F hL hH hT hN φ) = mkHom F' hT' hN' (Ψ F' hL' hH' hT' hN' φ') := by
    obtain ⟨p, k, k', he⟩ := (mkHom_eq_mkHom_iff' φ φ').1 e
    rw [← mkHom_tr k, ← mkHom_tr k', htr, htr, he]
  choose F hL hH hT hN φ hφ using hrep
  let σ₀ : (L ⟶ H) →+ (T ⟶ N) := AddMonoidHom.mk' (fun q ↦
    mkHom (F q) (hT q) (hN q) (Ψ _ (hL q) (hH q) (hT q) (hN q) (φ q))) (by
      intro q q'
      obtain ⟨m, hm, hm'⟩ := exists_ge_ge (F q) (F q')
      have e : q + q' = mkHom m ((hL q).trans hm) ((hH q).trans hm)
          (S.tr hm (φ q) + S.tr hm' (φ q')) := by
        rw [← hadd, mkHom_tr, mkHom_tr, ← hφ, ← hφ]
      rw [hind _ _ _ _ _ _ ((hL q).trans hm) ((hH q).trans hm) ((hT q).trans hm)
        ((hN q).trans hm) _ _ ((hφ _).symm.trans e), map_add, ← hadd, ← htr, ← htr,
        mkHom_tr, mkHom_tr])
  have hσ₀ (F' : I) (hL' : L.stage ≤ F') (hH' : H.stage ≤ F') (hT' : T.stage ≤ F')
      (hN' : N.stage ≤ F') (φ' : L.toStage hL' ⟶ H.toStage hH') :
      σ₀ (mkHom F' hL' hH' φ') = mkHom F' hT' hN' (Ψ F' hL' hH' hT' hN' φ') :=
    hind _ _ _ _ _ _ _ _ _ _ _ _ (hφ _).symm
  have hbij : Function.Bijective σ₀ := by
    constructor
    · intro q q' e
      obtain ⟨m, hm, hm'⟩ := exists_ge_ge (F q) (F q')
      have e' : mkHom m ((hT q).trans hm) ((hN q).trans hm)
          (Ψ m _ _ ((hT q).trans hm) ((hN q).trans hm) (S.tr hm (φ q))) =
          mkHom m ((hT q').trans hm') ((hN q').trans hm')
          (Ψ m _ _ ((hT q').trans hm') ((hN q').trans hm') (S.tr hm' (φ q'))) := by
        rw [← hσ₀, ← hσ₀, mkHom_tr, mkHom_tr, ← hφ, ← hφ]
        exact e
      obtain ⟨p, k, k', he⟩ := (mkHom_eq_mkHom_iff' _ _).1 e'
      rw [htr, htr] at he
      rw [hφ q, hφ q', ← mkHom_tr hm, ← mkHom_tr hm']
      exact (mkHom_eq_mkHom_iff' _ _).2 ⟨p, k, k', (Ψ _ _ _ _ _).injective he⟩
    · intro f
      obtain ⟨m, hTm, hNm⟩ := exists_ge_ge T.stage N.stage
      obtain ⟨F', hmF, hT', hN', ψ, rfl⟩ := exists_le_mkHom_eq f m
      obtain ⟨F'', hF', hLH⟩ := exists_ge_ge F' (commonStage L.stage H.stage)
      refine ⟨mkHom F'' ((le_commonStage_left _ _).trans hLH)
        ((le_commonStage_right _ _).trans hLH)
        ((Ψ F'' _ _ (hT'.trans hF') (hN'.trans hF')).symm (S.tr hF' ψ)), ?_⟩
      rw [hσ₀ _ _ _ (hT'.trans hF') (hN'.trans hF'), AddEquiv.apply_symm_apply, mkHom_tr]
  exact ⟨AddEquiv.ofBijective σ₀ hbij, hσ₀⟩


omit [∀ i, Preadditive (C i)] in
/-- Descended bijections are compatible with precomposition as soon as their stagewise
bijections are compatible with the representatives of the precomposed arrows. -/
theorem homAddEquiv_descent_comp {L L' H T T' N : S.PairCategory}
    (σ : (L ⟶ H) ≃+ (T ⟶ N)) (σ' : (L' ⟶ H) ≃+ (T' ⟶ N))
    (Ψ : ∀ (F : I) (hL : L.stage ≤ F) (hH : H.stage ≤ F) (hT : T.stage ≤ F)
      (hN : N.stage ≤ F),
      (L.toStage hL ⟶ H.toStage hH) → (T.toStage hT ⟶ N.toStage hN))
    (Ψ' : ∀ (F : I) (hL : L'.stage ≤ F) (hH : H.stage ≤ F) (hT : T'.stage ≤ F)
      (hN : N.stage ≤ F), (L'.toStage hL ⟶ H.toStage hH) → (T'.toStage hT ⟶ N.toStage hN))
    (hσ : ∀ (F : I) (hL : L.stage ≤ F) (hH : H.stage ≤ F)
      (hT : T.stage ≤ F) (hN : N.stage ≤ F) (φ : L.toStage hL ⟶ H.toStage hH),
      σ (mkHom F hL hH φ) = mkHom F hT hN (Ψ F hL hH hT hN φ))
    (hσ' : ∀ (F : I) (hL : L'.stage ≤ F) (hH : H.stage ≤ F)
      (hT : T'.stage ≤ F) (hN : N.stage ≤ F) (φ : L'.toStage hL ⟶ H.toStage hH),
      σ' (mkHom F hL hH φ) = mkHom F hT hN (Ψ' F hL hH hT hN φ))
    (f : L' ⟶ L) (t : T' ⟶ T)
    (hft : ∀ (F : I) (hL' : L'.stage ≤ F) (hL : L.stage ≤ F)
      (f₀ : L'.toStage hL' ⟶ L.toStage hL), f = mkHom F hL' hL f₀ →
      ∀ (hT' : T'.stage ≤ F) (hT : T.stage ≤ F), ∃ t₀ : T'.toStage hT' ⟶ T.toStage hT,
        t = mkHom F hT' hT t₀ ∧ ∀ (hH : H.stage ≤ F) (hN : N.stage ≤ F)
          (φ : L.toStage hL ⟶ H.toStage hH),
          Ψ' F hL' hH hT' hN (f₀ ≫ φ) = t₀ ≫ Ψ F hL hH hT hN φ)
    (q : L ⟶ H) : σ' (f ≫ q) = t ≫ σ q := by
  obtain ⟨m₁, hT₁, hT'₁⟩ := exists_ge_ge T.stage T'.stage
  obtain ⟨m, hm₁, hN₁⟩ := exists_ge_ge m₁ N.stage
  obtain ⟨n, hmn, hL', hL, -, hH, f₀, φ, rfl, rfl⟩ := exists_common_stage f q m
  obtain ⟨t₀, rfl, ht₀⟩ := hft n hL' hL f₀ rfl (hT'₁.trans (hm₁.trans hmn))
    (hT₁.trans (hm₁.trans hmn))
  rw [mkHom_comp_mkHom, hσ' _ _ _ (hT'₁.trans (hm₁.trans hmn)) (hN₁.trans hmn),
    hσ _ _ _ (hT₁.trans (hm₁.trans hmn)) (hN₁.trans hmn), mkHom_comp_mkHom, ht₀]
end CategoryTheory.StageSystem.PairCategory
