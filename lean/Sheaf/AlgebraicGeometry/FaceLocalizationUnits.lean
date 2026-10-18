/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Units in a face localization

Source: Illusie–Laszlo–Orgogozo, Exposé VIII, 3.1.1–3.1.2, printed pp. 98–99
(blueprint: lem-trf-face-localization-units).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Algebra

/-- For an integral commutative additive monoid, the units of the localization at a
face are precisely the differences of elements of that face. Source: Illusie–Laszlo–
Orgogozo, Exposé VIII, 3.1.1–3.1.2, printed pp. 98–99
(blueprint: lem-trf-face-localization-units). The proof uses the two displayed elementary steps:
face elements and their negatives are units, and an inverse represented by `q' - f'`
forces `q + q' = f + f'`, hence `q,q'` lie in the face by integrality and the face
condition.
-/
theorem isAddUnit_addLocalization_iff_face
    {Q : Type u} [AddCommMonoid Q] (hQ :
      Function.Injective
        (fun q : Q =>
          AddLocalization.mk q (⟨0, AddSubmonoid.mem_top 0⟩ :
            (⊤ : AddSubmonoid Q))))
    (F : AddSubmonoid Q)
    (hF : ∀ a b : Q, a + b ∈ F → a ∈ F ∧ b ∈ F)
    (x : AddLocalization F) :
    IsAddUnit x ↔
      ∃ f₁ f₂ : F, x = AddLocalization.mk (f₁ : Q) f₂ := by
  sorry

end Algebra
