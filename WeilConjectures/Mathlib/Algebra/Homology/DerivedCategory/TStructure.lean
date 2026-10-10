/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!

# Objects of a derived category with homology concentrated in an interval

For an abelian category `C`, this file records the property that an object of `D(C)` has
homology in degrees `[a, b]` only, expressed through the canonical t-structure
`DerivedCategory.TStructure.t` so that the whole t-structure API applies to it.

## Main definitions

- `DerivedCategory.homologyConcentratedIn`: homology concentrated in `[a, b]`.

## Main statements

- `DerivedCategory.exists_homologyConcentratedIn_iff_bounded`: an object is bounded exactly
  when its homology is concentrated in some interval.
- `DerivedCategory.prop_of_bounded`: *dévissage*, a triangulated subcategory of `D(C)`
  containing the objects of `C` satisfying `P`, placed in degree `0`, contains every bounded
  object all of whose homology objects satisfy `P`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- An object of `D(C)` has *homology concentrated in `[a, b]`* if it is both `≥ a` and `≤ b`
for the canonical t-structure `DerivedCategory.TStructure.t`, that is, if its homology
objects vanish outside the interval `[a, b]`. -/
def homologyConcentratedIn (a b : ℤ) : ObjectProperty (DerivedCategory C) :=
  fun M ↦ TStructure.t.IsGE M a ∧ TStructure.t.IsLE M b

lemma homologyConcentratedIn_iff (a b : ℤ) (M : DerivedCategory C) :
    homologyConcentratedIn a b M ↔ TStructure.t.IsGE M a ∧ TStructure.t.IsLE M b :=
  Iff.rfl

/-- Widening the interval preserves homology concentration. -/
lemma homologyConcentratedIn.mono {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b')
    {M : DerivedCategory C} (hM : homologyConcentratedIn a b M) :
    homologyConcentratedIn a' b' M := by
  obtain ⟨h₁, h₂⟩ := hM
  exact ⟨TStructure.t.isGE_of_ge M a' a ha, TStructure.t.isLE_of_le M b b' hb⟩

/-- An object of `D(C)` is bounded exactly when its homology is concentrated in some
interval. -/
lemma exists_homologyConcentratedIn_iff_bounded (M : DerivedCategory C) :
    (∃ a b : ℤ, homologyConcentratedIn a b M) ↔ TStructure.t.bounded M := by
  constructor
  · rintro ⟨a, b, ha, hb⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a, b, ha, hb⟩

/-- For a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` and `n : ℤ` such that the homology
objects of `X₃` in degrees `n - 1` and `n` vanish, the map `Hⁿ X₁ ⟶ Hⁿ X₂` is an isomorphism. -/
lemma isIso_homologyMap_mor₁ (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₀ : IsZero ((homologyFunctor C n₀).obj T.obj₃))
    (h₁ : IsZero ((homologyFunctor C n₁).obj T.obj₃)) :
    IsIso ((homologyFunctor C n₁).map T.mor₁) := by
  have := (HomologySequence.mono_homologyMap_mor₁_iff T hT n₀ n₁ h).2 (h₀.eq_of_src _ _)
  have := (HomologySequence.epi_homologyMap_mor₁_iff T hT n₁).2 (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- For a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` and `n : ℤ` such that the homology
objects of `X₁` in degrees `n` and `n + 1` vanish, the map `Hⁿ X₂ ⟶ Hⁿ X₃` is an isomorphism. -/
lemma isIso_homologyMap_mor₂ (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₀ : IsZero ((homologyFunctor C n₀).obj T.obj₁))
    (h₁ : IsZero ((homologyFunctor C n₁).obj T.obj₁)) :
    IsIso ((homologyFunctor C n₀).map T.mor₂) := by
  have := (HomologySequence.mono_homologyMap_mor₂_iff T hT n₀).2 (h₀.eq_of_src _ _)
  have := (HomologySequence.epi_homologyMap_mor₂_iff T hT n₀ n₁ h).2 (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- **Dévissage of bounded complexes.** Let `Q` be a triangulated subcategory of `D(C)` and
`P` a property of objects of `C` such that `Q` contains the objects of `C`
satisfying `P`, placed in degree `0`. Then `Q` contains every object of `D(C)` whose homology
is concentrated in `[a, b]` and satisfies `P` there: by induction on `b - a`, using the
truncation triangle `τ_{< b} M ⟶ M ⟶ τ_{≥ b} M ⟶`, whose third term is `H^b M` placed in
degree `b`. -/
lemma prop_of_isGE_of_isLE (Q : ObjectProperty (DerivedCategory C)) [Q.IsTriangulated]
    [Q.IsClosedUnderIsomorphisms] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ X, P X → Q ((singleFunctor C 0).obj X)) (n : ℕ) :
    ∀ (a : ℤ) (M : DerivedCategory C), M.IsGE a → M.IsLE (a + n - 1) →
      (∀ q, a ≤ q → q < a + n → P ((homologyFunctor C q).obj M)) → Q M := by
  induction n with
  | zero =>
    intro a M _ _ _
    have : M.IsLE (a - 1) := by simpa using ‹M.IsLE (a + ↑(0 : ℕ) - 1)›
    exact Q.prop_of_isZero (TStructure.t.isZero M (a - 1) a (by lia))
  | succ n ih =>
    intro a M _ _ hM
    set b : ℤ := a + n
    have hT := TStructure.t.triangleLTGE_distinguished b M
    -- the third term is `H^b M` placed in degree `b`
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
    have h₃ : Q ((TStructure.t.triangleLTGE b).obj M).obj₃ := by
      refine Q.prop_of_iso
        (e ≪≫ (((singleFunctors C).shiftIso (-b) b 0 (by lia)).app Y).symm).symm ?_
      exact Q.le_shift (-b) _ (hP Y hY)
    -- the first term is handled by induction
    have h₁ : Q ((TStructure.t.triangleLTGE b).obj M).obj₁ := by
      refine ih a _ ?_ ?_ fun q hq hq' ↦ ?_
      · exact inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj M) a)
      · exact TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      · have : IsIso ((homologyFunctor C q).map ((TStructure.t.triangleLTGE b).obj M).mor₁) :=
          isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
            (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
        exact P.prop_of_iso
          (asIso ((homologyFunctor C q).map ((TStructure.t.triangleLTGE b).obj M).mor₁)).symm
          (hM q hq (by lia))
    obtain ⟨M', hM', ⟨e'⟩⟩ := Q.ext_of_isTriangulatedClosed₂' _ hT h₁ h₃
    exact Q.prop_of_iso e'.symm hM'

/-- **Dévissage of bounded complexes.** Let `Q` be a triangulated subcategory of `D(C)` and
`P` a property of objects of `C` such that `Q` contains the objects of `C` satisfying `P`,
placed in degree `0`. Then `Q` contains every bounded object of `D(C)` all of whose homology
objects satisfy `P`. -/
lemma prop_of_bounded (Q : ObjectProperty (DerivedCategory C)) [Q.IsTriangulated]
    [Q.IsClosedUnderIsomorphisms] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ X, P X → Q ((singleFunctor C 0).obj X)) (M : DerivedCategory C)
    (hM : TStructure.t.bounded M) (hMP : ∀ n, P ((homologyFunctor C n).obj M)) : Q M := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hM
  have : M.IsLE (a + ↑(b - a + 1).toNat - 1) :=
    TStructure.t.isLE_of_le M b _ (by lia)
  exact prop_of_isGE_of_isLE Q P hP (b - a + 1).toNat a M ha this fun q _ _ ↦ hMP q

section Amplitude

variable {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
  (Φ : DerivedCategory C ⥤ DerivedCategory D) [Φ.CommShift ℤ] [Φ.IsTriangulated] (d : ℤ)

omit [Φ.IsTriangulated] in
/-- If a triangulated functor `Φ : D(C) ⥤ D(D)` sends every object of `C` placed in degree `0`
into degrees `≤ d`, it sends every object of `C` placed in degree `n` into degrees `≤ n + d`. -/
lemma isLE_obj_singleFunctor_obj (hΦ : ∀ F : C, (Φ.obj ((singleFunctor C 0).obj F)).IsLE d)
    (F : C) (n : ℤ) : (Φ.obj ((singleFunctor C n).obj F)).IsLE (n + d) := by
  have := hΦ F
  have : TStructure.t.IsLE ((Φ.obj ((singleFunctor C 0).obj F))⟦-n⟧) (n + d) :=
    TStructure.t.isLE_shift _ d (-n) (n + d) (by lia)
  let e : (Φ.obj ((singleFunctor C 0).obj F))⟦-n⟧ ≅ Φ.obj ((singleFunctor C n).obj F) :=
    (Φ.commShiftIso (-n)).symm.app _ ≪≫
      Φ.mapIso (((singleFunctors C).shiftIso (-n) n 0 (by lia)).app F)
  exact TStructure.t.isLE_of_iso e (n + d)

/-- **Amplitude by dévissage.** If a triangulated functor `Φ : D(C) ⥤ D(D)` sends every object
of `C` placed in degree `0` into degrees `≤ d`, it sends every bounded object concentrated in
degrees `≤ n` into degrees `≤ n + d`: by induction on the length, using the truncation triangle
`τ_{< n} M ⟶ M ⟶ τ_{≥ n} M ⟶` whose third term is `Hⁿ M` placed in degree `n`. -/
lemma isLE_obj_of_isLE (hΦ : ∀ F : C, (Φ.obj ((singleFunctor C 0).obj F)).IsLE d)
    (M : DerivedCategory C) (hM : TStructure.t.bounded M) (n : ℤ) [M.IsLE n] :
    (Φ.obj M).IsLE (n + d) := by
  obtain ⟨⟨a, ha⟩, -⟩ := hM
  suffices h : ∀ (k : ℕ) (M : DerivedCategory C) (n : ℤ), M.IsGE (n - k) → M.IsLE n →
      (Φ.obj M).IsLE (n + d) by
    exact h (n - a).toNat M n (TStructure.t.isGE_of_ge M _ a (by lia)) inferInstance
  intro k
  induction k with
  | zero =>
    intro M n h₁ h₂
    have : M.IsGE n := by simpa using h₁
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE M n
    have := isLE_obj_singleFunctor_obj Φ d hΦ Y n
    exact TStructure.t.isLE_of_iso (Φ.mapIso e.symm) (n + d)
  | succ k ih =>
    intro M n h₁ h₂
    have hT := Φ.map_distinguished _ (TStructure.t.triangleLTGE_distinguished n M)
    refine TStructure.t.isLE₂ _ hT (n + d) ?_ ?_
    · have : ((TStructure.t.triangleLTGE n).obj M).obj₁.IsLE (n - 1) :=
        TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      have : ((TStructure.t.triangleLTGE n).obj M).obj₁.IsGE (n - 1 - k) := by
        have : M.IsGE (n - 1 - k) := TStructure.t.isGE_of_ge M _ (n - ↑(k + 1)) (by lia)
        exact inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT n).obj M) _)
      have := ih _ (n - 1) this inferInstance
      exact TStructure.t.isLE_of_le (Φ.obj ((TStructure.t.triangleLTGE n).obj M).obj₁)
        (n - 1 + d) (n + d) (by lia)
    · have : ((TStructure.t.triangleLTGE n).obj M).obj₃.IsLE n :=
        inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE n).obj M) n)
      have : ((TStructure.t.triangleLTGE n).obj M).obj₃.IsGE n :=
        inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncGE n).obj M) n)
      obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
        ((TStructure.t.triangleLTGE n).obj M).obj₃ n
      have := isLE_obj_singleFunctor_obj Φ d hΦ Y n
      exact TStructure.t.isLE_of_iso (Φ.mapIso e.symm) (n + d)

end Amplitude

end DerivedCategory
