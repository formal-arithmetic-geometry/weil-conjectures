/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.CategoryTheory.BrownRepresentabilityRightAdjoint
import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
import WeilConjectures.CategoryTheory.CompactGenerationEquivalence
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Objectwise Brown representability with small Hom sets

Source: Stacks Project, Derived Categories, Proposition 0A8G.
-/

@[expose] public section

universe w u₁ u₂ v₁ v₂

open CategoryTheory.Limits

namespace CategoryTheory

/-- For an exact coproduct-preserving functor with compactly generated source,
`Hom(F(-), Y)` is representable. The Hom types may live in unrelated universes,
provided both categories are locally small in the coproduct indexing universe.
Stacks Project, Derived Categories, Tags 0A8G and 0A8F. -/
theorem brownHomRepresentabilityLocallySmall
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [LocallySmall.{w} C] [LocallySmall.{w} D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] [IsTriangulated C] [IsTriangulated D]
    [HasCoproducts.{w} C] [HasCoproducts.{w} D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (hC : IsCompactlyGeneratedTriangulated.{w} C)
    (hF : ∀ I : Type w, PreservesColimitsOfShape (Discrete I) F) (Y : D) :
    (F.op ⋙ yoneda.obj Y).IsRepresentable := by
  let eC := ShrinkHoms.equivalence.{w} C
  let eD := ShrinkHoms.equivalence.{w} D
  obtain ⟨zC, sC, pC, aC, tC, iC, cC, hTC⟩ := triangulatedEquivalenceTransfer eC
  obtain ⟨zD, sD, pD, aD, tD, iD, cD, hTD⟩ := triangulatedEquivalenceTransfer eD
  let := zC
  let := sC
  let := pC
  let := aC
  let := tC
  let := iC
  let := cC
  let := zD
  let := sD
  let := pD
  let := aD
  let := tD
  let := iD
  let := cD
  let := eC.commShiftInverse ℤ
  let := eD.commShiftInverse ℤ
  let := hTC.1
  let := hTC.2
  let := hTD.1
  let := hTD.2
  let : HasCoproducts.{w} (ShrinkHoms C) :=
    fun _ ↦ Adjunction.hasColimitsOfShape_of_equivalence eC.inverse
  let : HasCoproducts.{w} (ShrinkHoms D) :=
    fun _ ↦ Adjunction.hasColimitsOfShape_of_equivalence eD.inverse
  have hCs := compactGenerationEquivalence eC hC
  let Fs := eC.inverse ⋙ F ⋙ eD.functor
  have hFs : ∀ I : Type w, PreservesColimitsOfShape (Discrete I) Fs := by
    intro I
    let := hF I
    dsimp [Fs]
    infer_instance
  have hAdj : Fs.IsLeftAdjoint := brownRepresentabilityRightAdjoint Fs hCs hFs
  have hAdj' : (F ⋙ eD.functor).IsLeftAdjoint :=
    (Functor.isLeftAdjoint_comp_iff_right eC.inverse (F ⋙ eD.functor)).mp hAdj
  let : F.IsLeftAdjoint :=
    (Functor.isLeftAdjoint_comp_iff_left F eD.functor).mp hAdj'
  exact ((Adjunction.ofIsLeftAdjoint F).representableBy Y).isRepresentable

end CategoryTheory
