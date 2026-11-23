/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ExactCouple.FilteredComplex


public import WeilConjectures.CategoryTheory.FilteredCohomologyImage
import WeilConjectures.CategoryTheory.FilteredNormalizedQuotientPresentation
import WeilConjectures.CategoryTheory.FilteredCohomologyImageNormalized

/-! # A cycle presentation of the graded cohomology image

## References

* Stacks Project, Tag 012Q, Equation 12.24.5.2.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

/-- The graded cohomology image is a quotient of the ambient cycles in a filtration step.

Stacks Project, Tag 012Q. -/
theorem cohomologyImage_graded_presentation
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K) (p n : ℤ) :
  let A := L.complexStep p n
  let A' := L.complexStep (p + 1) n
  let Z := (Subobject.pullback (K.d n (n + 1))).obj ⊥
  let B := imageSubobject (K.d (n - 1) n)
  Nonempty ((L.homologyFiltration n).gradedPiece p ≅
    cokernel ((Subobject.pullback (A ⊓ Z).arrow).obj
      ((A ⊓ B) ⊔ (A' ⊓ Z))).arrow) := by
  dsimp only
  obtain ⟨hBZ, ⟨e₀⟩⟩ := cohomologyImage_graded_normalized L p n
  obtain ⟨e₁⟩ := L.normalizedStationaryQuotient_presentation p n hBZ
  exact ⟨e₀ ≪≫ e₁⟩

end CategoryTheory.DecreasingFiltration
