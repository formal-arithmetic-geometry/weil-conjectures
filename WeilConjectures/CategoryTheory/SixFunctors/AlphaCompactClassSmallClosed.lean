/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.AlphaCompactObject
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.IsAlphaCompact.AlphaCompactObjectProperties
import WeilConjectures.CategoryTheory.IsAlphaCompact.AlphaCompactExtensions
import WeilConjectures.CategoryTheory.SixFunctors.AlphaCompactFactorThrough
import WeilConjectures.CategoryTheory.SixFunctors.SmallBoundedTriangulatedHull

/-! # Krause's maximal alpha-compact class identification -/

@[expose] public section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory

/-- Krause's maximal alpha-compact class is small and extension closed when
there is a small shift-closed perfect generating class of alpha-small objects.

Source: Krause, On Neeman's Well Generated Triangulated Categories (2001),
Lemma 5, pages 124--125.

Reference: https://ftp.gwdg.de/pub/misc/EMIS/journals/DMJDMV/vol-06/07.pdf, Lemma 5.
-/
theorem alphaCompactObjects_small_closed
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{v} C]
    (G : ObjectProperty C) [ObjectProperty.EssentiallySmall.{v} G]
    [G.IsStableUnderShift ℤ] (α : Cardinal.{v}) [Fact α.IsRegular]
    (hGsmall : ∀ X, G X → IsAlphaSmall X α)
    (hGfactor : G.IsCoproductFactorizationClass)
    (hGgen : ∀ (S : ObjectProperty C) [S.IsClosedUnderIsomorphisms] [S.IsTriangulated],
      (∀ (I : Type v) (Y : I → C), (∀ i, S (Y i)) → S (∐ Y)) →
      G ≤ S → ∀ X, S X) :
    ObjectProperty.EssentiallySmall.{v} (alphaCompactObjects C α) ∧
      (alphaCompactObjects C α).IsTriangulatedClosed₂ := by
  let := HasZeroObject.zero' C
  let S := alphaCompactObjects C α
  have : S.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨fun X hX ↦ hX.shift n⟩⟩
  have : S.ContainsZero := ⟨0, Limits.isZero_zero C, isAlphaCompact_zero α⟩
  have hclosed : S.IsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ ↦
    IsAlphaCompact.extension α T hT h₁ h₃)
  have : S.IsTriangulated := {}
  have hGS : G ≤ S := fun X hX ↦ ⟨G, hX, hGsmall, hGfactor⟩
  have hsum (I : Type v) (Y : I → C) (hI : HasCardinalLT I α)
      (hY : ∀ i, S (Y i)) : S (∐ Y) := IsAlphaCompact.coproduct α I Y hI hY
  obtain ⟨H, hsmall, hiso, htri, hGH, hHS, hHsum⟩ :=
    exists_small_bounded_triangulated_hull G S α hGS hsum
  have : ObjectProperty.EssentiallySmall.{v} H := hsmall
  have : H.IsClosedUnderIsomorphisms := hiso
  have : H.IsTriangulated := htri
  exact ⟨ObjectProperty.EssentiallySmall.of_le
    (alphaCompactObjects_le_retractClosure α G H hHS hHsum hGH hGgen), hclosed⟩

end CategoryTheory
