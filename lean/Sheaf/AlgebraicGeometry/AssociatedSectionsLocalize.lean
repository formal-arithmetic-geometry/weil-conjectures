/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Principal localization of an associated module sheaf

Source: Weil conjectures blueprint, sec-abelian-varieties, sk-prop-av-pqf-finite,
node pqf-lem-associated-sections-localize (blueprint: pqf-lem-associated-sections-localize).

The spectrum of `B ⊗[A] Localization.Away a` is canonically the principal open
`D(φ a)` of `Spec B`, by `IsLocalization.tensor`. We express sections on that spectrum
as sections of the original associated sheaf on this principal open.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite TensorProduct

namespace AlgebraicGeometry

/-- Restriction identifies the base change of a module with sections of its associated
sheaf on the principal open defined by the image of the element being inverted.
Source: Weil conjectures blueprint, node pqf-lem-associated-sections-localize
(blueprint: pqf-lem-associated-sections-localize).

Proof:
1. Write `b = φ a`. The ring localization base-change theorem
   (`lem-weil-pbc-localization-base-change`, `IsLocalization.tensor`) identifies
   `B ⊗[A] A_a` with `B_b`, whose spectrum is `D(b)`.
2. The principal-open sections formula (`lem-weil-pbc-spec-module-tilde-sections`,
   `tilde.toOpen` and its `IsLocalizedModule.Away` instance) identifies sections of
   `tilde M` on `D(b)` with `M_b`, sending `m/b^n` to `b⁻ⁿ τ(m)`.
3. The universal properties identify `M ⊗[A] A_a` with `M_b`, sending
   `m ⊗ (x/a^n)` to `φ(x)m/b^n`. Compose these identifications. On `m ⊗ 1` the
   resulting map is `tilde.toOpen`, so the isomorphism is induced by restriction.
No finiteness or coherence hypothesis on `M` is required. -/
theorem associated_sections_localize
    {A : Type v} [CommRing A] {B : CommRingCat.{u}}
    (φ : A →+* B) (M : ModuleCat.{u} B) (a : A) :
    ∃ e : ((ModuleCat.restrictScalars φ).obj M ⊗[A] Localization.Away a) ≃ₗ[A]
      (ModuleCat.restrictScalars φ).obj
        ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj
          (op (PrimeSpectrum.basicOpen (φ a)))),
      ∀ m : M, e (m ⊗ₜ[A] (1 : Localization.Away a)) =
        tilde.toOpen M (PrimeSpectrum.basicOpen (φ a)) m := by
  sorry

end AlgebraicGeometry
