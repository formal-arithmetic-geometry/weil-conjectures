/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# The natural local-ring map of a fibre

For a prime `Q` of the fibre ring `κ(p) ⊗[A] B` with contraction `q` in `B`, the canonical map
`B_q → (κ(p) ⊗[A] B)_Q` is surjective with kernel `p B_q`.

## Implementation details

Mathlib uses `κ(p) ⊗[A] B` for the fibre, so `j(b) = 1 ⊗ b`. The proof identifies the fibre
with a quotient of `(A \ p)⁻¹ B` via `Ideal.Fiber.algEquivAux₁` and follows the construction of
`Ideal.Fiber.algEquivAux₂`, keeping `B` as the scalar ring, to obtain an equivalence
`C_Q ≃ₐ[B] B_q / p B_q`; localization uniqueness identifies it with the local-ring map.

## References

* [Stacks, Tag 0H9M], [Stacks, Tag 00E6]
-/

@[expose] public section

universe u v

namespace Ideal

/-- The canonical map from `B_q` to the local ring of the fibre at `Q` is surjective,
with kernel `p B_q`, and induces the quotient isomorphism with its natural fraction formula. -/
theorem Fiber.localRingHom_surjective_ker_quotientEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (Q : Ideal (p.Fiber B)) [Q.IsPrime] :
    let j : B →+* p.Fiber B := Algebra.TensorProduct.includeRight.toRingHom
    let q : Ideal B := Q.comap j
    let θ := Localization.localRingHom q Q j rfl
    let I : Ideal (Localization.AtPrime q) :=
      (p.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime q))
    (∀ (b : B) (s : q.primeCompl),
      θ (Localization.mk b s) = Localization.mk (j b) ⟨j s, s.property⟩) ∧
    Function.Surjective θ ∧ RingHom.ker θ = I ∧
    ∃ e : (Localization.AtPrime q ⧸ I) ≃+* Localization.AtPrime Q,
      ∀ x : Localization.AtPrime q, e (Ideal.Quotient.mk I x) = θ x := by
  let j : B →+* p.Fiber B := Algebra.TensorProduct.includeRight.toRingHom
  let q := Q.comap j
  let I := (p.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime q))
  let : Algebra B (p.Fiber B) := Algebra.TensorProduct.rightAlgebra
  let D := Localization (Algebra.algebraMapSubmonoid B p.primeCompl)
  let pB := p.map (algebraMap A B)
  let E := B ⧸ pB
  let e₁ : p.Fiber B ≃ₐ[B] D ⧸ pB.map (algebraMap B D) := Fiber.algEquivAux₁ p
  let Q' : Ideal (D ⧸ pB.map (algebraMap B D)) := Q.comap e₁.symm
  have : (Q'.under E).LiesOver q := under_liesOver_of_liesOver E Q' (Q.under B)
  have : Algebra.algebraMapSubmonoid E q.primeCompl = (Q'.under E).primeCompl :=
    algebraMapSubmonoid_primeCompl_of_liesOver_surjective
      (Q'.under E) q Quotient.mk_surjective
  have : IsLocalization (Algebra.algebraMapSubmonoid E q.primeCompl)
      (Localization.AtPrime Q') := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid E (Algebra.algebraMapSubmonoid B p.primeCompl))
      (Localization.AtPrime Q') Q'
  let e : Localization.AtPrime Q ≃ₐ[B] Localization.AtPrime q ⧸ I :=
    (Localization.localAlgEquiv Q' Q e₁.symm rfl).symm.trans
      ((IsLocalization.algEquiv (Algebra.algebraMapSubmonoid E q.primeCompl)
        (Localization.AtPrime Q') (Localization.AtPrime q ⧸ I)).restrictScalars B)
  let θ := Localization.localRingHom q Q j rfl
  have hθ : θ = e.symm.toRingHom.comp (Quotient.mk I) := by
    apply Localization.localRingHom_unique
    intro b
    change e.symm (algebraMap B (Localization.AtPrime q ⧸ I) b) = _
    exact e.symm.commutes b
  have he (x : Localization.AtPrime q) :
      e.symm (Quotient.mk I x) = θ x := by
    rw [hθ]
    rfl
  refine ⟨?_, ?_, ?_, e.symm.toRingEquiv, he⟩
  · intro b s
    exact Localization.localRingHom_mk q Q j rfl b s
  · intro y
    obtain ⟨x, hx⟩ := Quotient.mk_surjective (e y)
    refine ⟨x, ?_⟩
    rw [← he, hx, e.symm_apply_apply]
  · ext x
    change θ x = 0 ↔ x ∈ I
    rw [← he]
    constructor
    · intro h
      apply Quotient.eq_zero_iff_mem.mp
      apply e.symm.injective
      simpa only [map_zero] using h
    · intro h
      rw [Quotient.eq_zero_iff_mem.mpr h, map_zero]

end Ideal
