/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.FilteredCohomologyImage
import Sheaf.CategoryTheory.FilteredNormalizedQuotientPresentation

/-! # Normalized presentation of the cohomology image graded piece

Source: Stacks Project, Tag 012Q.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

/-- The image filtration graded piece is represented by the normalized cycle quotient.
Source: Stacks Project, Tag 012Q, final quotient calculation.
(blueprint: lem-sp-filtered-cohomology-image-normalized-quotient).
-/
theorem cohomologyImage_graded_normalized
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K) (p n : ℤ) :
  let A := L.complexStep p n
  let A' := L.complexStep (p + 1) n
  let Z := (Subobject.pullback (K.d n (n + 1))).obj ⊥
  let B := imageSubobject (K.d (n - 1) n)
  let q := (L.complexQuotientπ p (p + 1) (Int.le_add_one le_rfl)).f n
  let P := Subobject.pullback ((L.step p).arrow.f n)
  let Zbar := (Subobject.«exists» q).obj (P.obj ((A ⊓ Z) ⊔ A'))
  let Bbar := (Subobject.«exists» q).obj (P.obj ((A ⊓ B) ⊔ A'))
  ∃ hBZ : Bbar ≤ Zbar,
    Nonempty ((L.cohomologyImage n).gradedPiece p ≅
      cokernel (Subobject.ofLE Bbar Zbar hBZ)) := by sorry


end CategoryTheory.DecreasingFiltration
