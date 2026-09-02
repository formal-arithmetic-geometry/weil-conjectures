/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-!

# The conjugate of the canonical isomorphism of two left adjoints

If `F` and `F'` are both left adjoint to `G`, the canonical isomorphism
`CategoryTheory.Adjunction.leftAdjointUniq` between them is, by construction, the
isomorphism conjugate to the identity of `G`. This file records that in the form used for
comparing mates: conjugating `Adjunction.leftAdjointUniq` in either direction gives the
identity of `G`.

## Main results

- `CategoryTheory.conjugateEquiv_leftAdjointUniq_hom` and
  `CategoryTheory.conjugateEquiv_leftAdjointUniq_inv`: the conjugates of the two
  directions of `Adjunction.leftAdjointUniq` are the identity of the common right adjoint.

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] {F F' : C ⥤ D} {G : D ⥤ C}

/-- The conjugate of `Adjunction.leftAdjointUniq adj₁ adj₂` is the identity of the common
right adjoint. -/
lemma conjugateEquiv_leftAdjointUniq_hom (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G) :
    conjugateEquiv adj₂ adj₁ (Adjunction.leftAdjointUniq adj₁ adj₂).hom = 𝟙 G := by
  simp [Adjunction.leftAdjointUniq]

/-- The conjugate of the inverse of `Adjunction.leftAdjointUniq adj₁ adj₂` is the identity
of the common right adjoint. -/
lemma conjugateEquiv_leftAdjointUniq_inv (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G) :
    conjugateEquiv adj₁ adj₂ (Adjunction.leftAdjointUniq adj₁ adj₂).inv = 𝟙 G := by
  simp [Adjunction.leftAdjointUniq]

end CategoryTheory
