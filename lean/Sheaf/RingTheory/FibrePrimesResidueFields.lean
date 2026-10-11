/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Primes and residue fields of a fibre ring

Source: Stacks Project, Tags 00E6 and 0H9M
(blueprint: lem-weil-pbc-fibre-ring-primes-residue-fields).
-/

universe u v

open scoped TensorProduct

namespace PrimeSpectrum

/-- The primes of the fibre ring `p.Fiber B = κ(p) ⊗[A] B` correspond, preserving and
reflecting inclusions, to primes of `B` over `p`, and their residue fields are identified
by the tensor evaluation map.
Source: Stacks Project, Tags 00E6 and 0H9M
(blueprint: lem-weil-pbc-fibre-ring-primes-residue-fields).

Mathlib's fibre `Ideal.Fiber` is `κ(p) ⊗[A] B`; tensor symmetry identifies its
`j(b) = 1 ⊗ b` (`includeRight`) with the source's `b ⊗ 1`, and `ψ_q(λ ⊗ b) = λ̄ b̄`.

Proof:
1. Apply `lem-weil-pbc-fibre-ring-primes-bijection` (the order correspondence of Tag 00E6)
   to obtain contraction along `j` and its inverse, the kernel of `ψ`.
2. For `Q = ker ψ`, `lem-weil-pbc-fibre-ring-residue-field-iso` identifies `κ(q)` with
   `κ(Q)` via the local map induced by `j`. Let `θ` be the inverse. Canonical residue maps
   satisfy `π_Q ∘ j = ι ∘ π_q` (`def-weil-pbc-localization-at-prime`).
3. Thus `θ ∘ π_Q` agrees with `ψ` on `j(b)`.
4. On the `κ(p)` factor, the two maps agree on the image of `A`, by tensor balancing. Every
   residue-field element is a fraction of images of elements of `A`, with denominator
   outside `p` (`def-weil-pbc-localization-at-prime`), so they agree on all of `κ(p)`.
5. Multiplicativity gives agreement on pure tensors, and additive generation gives
   `θ ∘ π_Q = ψ`, as required. -/
theorem fibre_primes_residue_fields
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (p : PrimeSpectrum A) :
    let j : B →+* p.asIdeal.Fiber B := Algebra.TensorProduct.includeRight.toRingHom
    let F := PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}
    let ψ : (q : F) → p.asIdeal.Fiber B →+* q.1.asIdeal.ResidueField := fun q ↦
      (Algebra.TensorProduct.lift
        (Ideal.ResidueField.mapₐ p.asIdeal q.1.asIdeal (Algebra.ofId A B)
          congr($(q.2.symm).asIdeal))
        (IsScalarTower.toAlgHom A B q.1.asIdeal.ResidueField)
        (fun _ _ ↦ Commute.all _ _)).toRingHom
    ∃ e : PrimeSpectrum (p.asIdeal.Fiber B) ≃o F,
      (∀ Q, (e Q).1.asIdeal = Q.asIdeal.comap j) ∧
      (∀ q, (e.symm q).asIdeal = RingHom.ker (ψ q)) ∧
      (∀ q, ∃ θ : (e.symm q).asIdeal.ResidueField ≃+* q.1.asIdeal.ResidueField,
        θ.toRingHom.comp (algebraMap (p.asIdeal.Fiber B) (e.symm q).asIdeal.ResidueField) =
          ψ q) := by
  sorry

end PrimeSpectrum
