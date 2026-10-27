/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude

/-!

# Finite Tor amplitude is a triangulated property

Let `C` be a monoidal closed braided Grothendieck abelian category with functorial flat
resolutions. The objects of `D(C)` of finite Tor amplitude form a triangulated subcategory: the
derived tensor product `- ⊗ᴸ F` is a triangulated functor, and concentration of homology in an
interval is stable under shifts and under extensions, with the interval shifted and widened.

## Main results

- `DerivedCategory.isTriangulated_finiteTorAmplitude`: finite Tor amplitude is a triangulated
  property of objects of `D(C)`.
- `DerivedCategory.torAmplitudeIn_obj₁_of_distTriang`: the Tor amplitude of the first vertex of
  a distinguished triangle, from those of the other two.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory ZeroObject

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

local instance : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

variable [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

/-- Finite Tor amplitude is a triangulated property of objects of `D(C)`: the derived tensor
product `- ⊗ᴸ F` is a triangulated functor, and concentration in an interval is stable under
shifts and under extensions, with the interval shifted and widened. -/
instance isTriangulated_finiteTorAmplitude : (finiteTorAmplitude C).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, 0, 0, fun F ↦ by
    have h : IsZero ((0 : DerivedCategory C) ⊗ (singleFunctor C 0).obj F) :=
      Functor.map_isZero ((curriedTensor (DerivedCategory C)).flip.obj
        ((singleFunctor C 0).obj F)) (isZero_zero _)
    exact ⟨(isGE_iff _ _).2 fun q _ ↦ Functor.map_isZero _ h,
      (isLE_iff _ _).2 fun q _ ↦ Functor.map_isZero _ h⟩⟩
  isStableUnderShiftBy n := ⟨fun M ⟨a, b, h⟩ ↦ ⟨a - n, b - n, fun F ↦ by
    obtain ⟨h₁, h₂⟩ := h F
    let e := (((curriedTensor (DerivedCategory C)).flip.obj
      ((singleFunctor C 0).obj F)).commShiftIso n).app M
    have hge := TStructure.t.isGE_shift (M ⊗ (singleFunctor C 0).obj F) a n (a - n)
    have hle := TStructure.t.isLE_shift (M ⊗ (singleFunctor C 0).obj F) b n (b - n)
    exact ⟨@Triangulated.TStructure.isGE_of_iso _ _ _ _ _ _ _ TStructure.t _ _ e.symm (a - n) hge,
      @Triangulated.TStructure.isLE_of_iso _ _ _ _ _ _ _ TStructure.t _ _ e.symm (b - n) hle⟩⟩⟩
  ext₂' T hT := by
    rintro ⟨a, b, h₁⟩ ⟨c, d, h₃⟩
    refine ObjectProperty.le_isoClosure _ _ ⟨min a c, max b d, fun F ↦ ?_⟩
    let G := (curriedTensor (DerivedCategory C)).flip.obj ((singleFunctor C 0).obj F)
    obtain ⟨g₁, l₁⟩ := (h₁ F).mono (min_le_left a c) (le_max_left b d)
    obtain ⟨g₃, l₃⟩ := (h₃ F).mono (min_le_right a c) (le_max_right b d)
    exact ⟨TStructure.t.isGE₂ _ (G.map_distinguished _ hT) _ g₁ g₃,
      TStructure.t.isLE₂ _ (G.map_distinguished _ hT) _ l₁ l₃⟩

variable {C} in
/-- Tor amplitude is stable under extensions, with the interval shifted: for a distinguished
triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁[1]` with `T₂` of Tor amplitude in `[a, b]` and `T₃` of Tor amplitude
in `[a, e]`, where `b ≤ e + 1`, the first vertex `T₁` has Tor amplitude in `[a, e + 1]`: the
derived tensor product `- ⊗ᴸ F` is a triangulated functor. -/
lemma torAmplitudeIn_obj₁_of_distTriang (T : Pretriangulated.Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) {a b e : ℤ} (hbe : b ≤ e + 1) (h₂ : torAmplitudeIn C a b T.obj₂)
    (h₃ : torAmplitudeIn C a e T.obj₃) : torAmplitudeIn C a (e + 1) T.obj₁ := fun F ↦
  homologyConcentratedIn_obj₁_of_distTriang _
    (((curriedTensor (DerivedCategory C)).flip.obj ((singleFunctor C 0).obj F)).map_distinguished
      _ hT) hbe (h₂ F) (h₃ F)

end DerivedCategory
