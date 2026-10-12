/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Amplitude of a triangulated functor on bounded complexes, by dévissage

Let `F : D(C) ⥤ D(D)` be a triangulated functor and `P` a property of objects of `C` such that
`F` sends every object of `C` satisfying `P`, placed in degree `0`, to an object with homology
in `[0, c]`. Then `F` sends every object with homology concentrated in `[a, b]` and satisfying
`P` there to an object with homology in `[a, b + c]`
(`DerivedCategory.homologyConcentratedIn_obj_of_devissage`).

The proof is the dévissage of `DerivedCategory.prop_of_isGE_of_isLE`: induction on `b - a`
along the truncation triangle `τ_{< b} M ⟶ M ⟶ (H^b M)[-b] ⟶`. This is the amplitude part of
the finite-filtration argument of the blueprint (`lem-sp-finite-filtration-induction`), used for
`prop-weil-pbc-restriction-direct-image`.

-/

@[expose] public section

universe w w' v v' u u'

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ] [F.IsTriangulated]
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (c : ℤ)

/-- **Dévissage for amplitudes**, the inductive form: if `F` sends the objects of `C`
satisfying `P`, placed in degree `0`, to objects with homology in `[0, c]`, then `F` sends an
object with homology in `[a, a + n - 1]` satisfying `P` to an object with homology in
`[a, a + n - 1 + c]`. -/
lemma homologyConcentratedIn_obj_of_isGE_of_isLE
    (hP : ∀ X, P X → homologyConcentratedIn 0 c (F.obj ((singleFunctor C 0).obj X)))
    (n : ℕ) : ∀ (a : ℤ) (M : DerivedCategory C), M.IsGE a → M.IsLE (a + n - 1) →
      (∀ q, a ≤ q → q < a + n → P ((homologyFunctor C q).obj M)) →
      homologyConcentratedIn a (a + n - 1 + c) (F.obj M) := by
  induction n with
  | zero =>
    intro a M _ _ _
    have : M.IsLE (a - 1) := by simpa using ‹M.IsLE (a + ↑(0 : ℕ) - 1)›
    have hz : IsZero (F.obj M) := F.map_isZero (TStructure.t.isZero M (a - 1) a (by lia))
    exact ⟨TStructure.t.isGE_of_isZero hz _, TStructure.t.isLE_of_isZero hz _⟩
  | succ n ih =>
    intro a M _ _ hM
    set b : ℤ := a + n
    have hT := TStructure.t.triangleLTGE_distinguished b M
    have : ((TStructure.t.triangleLTGE b).obj M).obj₃.IsLE b := by
      have : M.IsLE b := TStructure.t.isLE_of_le M (a + ↑(n + 1) - 1) _ (by lia)
      exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj M) b)
    have : ((TStructure.t.triangleLTGE b).obj M).obj₃.IsGE b := by
      infer_instance
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((TStructure.t.triangleLTGE b).obj M).obj₃ b
    have h₁ : IsZero ((homologyFunctor C (b + 1)).obj ((TStructure.t.triangleLTGE b).obj M).obj₁) :=
      isZero_of_isLE _ (b - 1) _ (by lia)
    have h₀ : IsZero ((homologyFunctor C b).obj ((TStructure.t.triangleLTGE b).obj M).obj₁) :=
      isZero_of_isLE _ (b - 1) _ (by lia)
    have := isIso_homologyMap_mor₂ _ hT b (b + 1) rfl h₀ h₁
    have hY : P Y := P.prop_of_iso
      (asIso ((homologyFunctor C b).map ((TStructure.t.triangleLTGE b).obj M).mor₂) ≪≫
        (homologyFunctor C b).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C b).app Y)
      (hM b (by lia) (by lia))
    -- the image of the third term is `F(Y[0])[-b]`, with homology in `[b, b + c]`
    have e₃ : F.obj ((TStructure.t.triangleLTGE b).obj M).obj₃ ≅
        (F.obj ((singleFunctor C 0).obj Y))⟦-b⟧ :=
      F.mapIso (e ≪≫ (((singleFunctors C).shiftIso (-b) b 0 (by lia)).app Y).symm) ≪≫
        (F.commShiftIso (-b)).app _
    obtain ⟨hY₀, hY₁⟩ := hP Y hY
    have h₃ : homologyConcentratedIn b (b + c)
        (F.obj ((TStructure.t.triangleLTGE b).obj M).obj₃) := by
      have := TStructure.t.isGE_shift (F.obj ((singleFunctor C 0).obj Y)) 0 (-b) b (by lia)
      have := TStructure.t.isLE_shift (F.obj ((singleFunctor C 0).obj Y)) c (-b) (b + c) (by lia)
      exact ⟨TStructure.t.isGE_of_iso e₃.symm b, TStructure.t.isLE_of_iso e₃.symm (b + c)⟩
    -- the first term is handled by induction
    have h₁ : homologyConcentratedIn a (a + n - 1 + c)
        (F.obj ((TStructure.t.triangleLTGE b).obj M).obj₁) := by
      refine ih a _ ?_ ?_ fun q hq hq' ↦ ?_
      · exact inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj M) a)
      · exact TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      · have : IsIso ((homologyFunctor C q).map ((TStructure.t.triangleLTGE b).obj M).mor₁) :=
          isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
            (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
        exact P.prop_of_iso
          (asIso ((homologyFunctor C q).map ((TStructure.t.triangleLTGE b).obj M).mor₁)).symm
          (hM q (by lia) (by lia))
    have hFT := F.map_distinguished _ hT
    obtain ⟨h₁₀, h₁₁⟩ := h₁
    obtain ⟨h₃₀, h₃₁⟩ := h₃
    have : TStructure.t.IsGE (F.obj ((TStructure.t.triangleLTGE b).obj M).obj₃) a :=
      TStructure.t.isGE_of_ge _ a b (by lia)
    have : TStructure.t.IsLE (F.obj ((TStructure.t.triangleLTGE b).obj M).obj₁)
        (a + ↑(n + 1) - 1 + c) :=
      TStructure.t.isLE_of_le _ (a + n - 1 + c) _ (by lia)
    have : TStructure.t.IsLE (F.obj ((TStructure.t.triangleLTGE b).obj M).obj₃)
        (a + ↑(n + 1) - 1 + c) :=
      TStructure.t.isLE_of_le _ (b + c) _ (by lia)
    exact ⟨TStructure.t.isGE₂ _ hFT a (by assumption) (by assumption),
      TStructure.t.isLE₂ _ hFT _ (by assumption) (by assumption)⟩

/-- **Dévissage for amplitudes.** Let `F : D(C) ⥤ D(D)` be triangulated and let `P` be a
property of objects of `C` such that `F` sends every object of `C` satisfying `P`, placed in
degree `0`, to an object with homology in `[0, c]`. Then for every object `M` with homology
concentrated in `[a, b]` whose homology objects satisfy `P`, the homology of `F M` is
concentrated in `[a, b + c]`. -/
lemma homologyConcentratedIn_obj_of_devissage
    (hP : ∀ X, P X → homologyConcentratedIn 0 c (F.obj ((singleFunctor C 0).obj X)))
    {a b : ℤ} (M : DerivedCategory C) (hM : homologyConcentratedIn a b M)
    (hMP : ∀ q, P ((homologyFunctor C q).obj M)) :
    homologyConcentratedIn a (b + c) (F.obj M) := by
  obtain ⟨ha, hb⟩ := hM
  by_cases hab : a ≤ b
  · have : M.IsLE (a + ↑(b - a + 1).toNat - 1) := TStructure.t.isLE_of_le M b _ (by lia)
    have h := homologyConcentratedIn_obj_of_isGE_of_isLE F P c hP (b - a + 1).toNat a M ha
      this fun q _ _ ↦ hMP q
    exact h.mono le_rfl (by lia)
  · have hz : IsZero (F.obj M) := F.map_isZero (TStructure.t.isZero M b a (by lia))
    exact ⟨TStructure.t.isGE_of_isZero hz _, TStructure.t.isLE_of_isZero hz _⟩

end DerivedCategory
