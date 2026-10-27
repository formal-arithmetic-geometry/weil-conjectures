/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Basic

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
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := isAddUnit_iff_exists_neg.mp hx
    induction x using AddLocalization.induction_on with
    | H x =>
      obtain ⟨q, f⟩ := x
      induction y using AddLocalization.induction_on with
      | H y =>
        obtain ⟨q', f'⟩ := y
        rw [AddLocalization.mk_add, ← AddLocalization.mk_zero] at hy
        obtain ⟨c, hc⟩ := AddLocalization.r_iff_exists.mp
          (AddLocalization.mk_eq_mk_iff.mp hy)
        have hsum : q + q' = (f : Q) + (f' : Q) := by
          apply hQ
          apply AddLocalization.mk_eq_mk_iff.mpr
          apply AddLocalization.r_iff_exists.mpr
          refine ⟨⟨(c : Q), AddSubmonoid.mem_top _⟩, ?_⟩
          simpa only [ZeroMemClass.coe_zero, zero_add, add_zero,
            AddSubmonoid.coe_add] using hc
        have hq : q ∈ F := (hF q q' (hsum ▸ F.add_mem f.property f'.property)).1
        exact ⟨⟨q, hq⟩, f, rfl⟩
  · rintro ⟨f₁, f₂, rfl⟩
    apply isAddUnit_iff_exists_neg.mpr
    refine ⟨AddLocalization.mk (f₂ : Q) f₁, ?_⟩
    rw [AddLocalization.mk_add, ← AddLocalization.mk_self (f₁ + f₂)]
    congr 1
    exact add_comm f₂ f₁

end Algebra
