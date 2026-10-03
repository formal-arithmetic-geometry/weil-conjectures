/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Nullstellensatz

/-!
# The Nullstellensatz for finitely generated algebras

Let `A` be a finitely generated algebra over an algebraically closed field `k`. Every maximal ideal
of `A` is the kernel of a `k`-algebra map `A →ₐ[k] k`, i.e. closed points of `Spec A` have residue
field `k`; and an element of `A` vanishing at every `k`-point is nilpotent.

## Main results

- `exists_algHom_ker_eq_of_isMaximal`: maximal ideals are kernels of `k`-points.
- `iInf_ker_algHom_eq_nilradical`: the vanishing principle.

## Blueprint

- `sk-i-geometry`: the Nullstellensatz and the vanishing principle.
-/

@[expose] public section

variable (k A : Type*) [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- Over an algebraically closed field `k`, every maximal ideal of a finitely generated
`k`-algebra is the kernel of a `k`-algebra map to `k`: closed points have residue field `k`.
(blueprint: `sk-i-geometry`) -/
theorem exists_algHom_ker_eq_of_isMaximal (𝔪 : Ideal A) [𝔪.IsMaximal] :
    ∃ φ : A →ₐ[k] k, RingHom.ker φ = 𝔪 := by
  let : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have : Module.Finite k (A ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing k _
  refine ⟨(IsAlgClosed.lift : (A ⧸ 𝔪) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k 𝔪), ?_⟩
  ext a
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- The vanishing principle: over an algebraically closed field `k`, an element of a finitely
generated `k`-algebra vanishing at every `k`-point is nilpotent.
(blueprint: `sk-i-geometry`) -/
theorem iInf_ker_algHom_eq_nilradical :
    (⨅ φ : A →ₐ[k] k, RingHom.ker φ) = nilradical A := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  refine le_antisymm ?_ ?_
  · rw [nilradical, Ideal.radical_eq_jacobson, Ideal.jacobson]
    refine le_sInf ?_
    rintro 𝔪 ⟨-, h𝔪⟩
    obtain ⟨φ, rfl⟩ := exists_algHom_ker_eq_of_isMaximal k A 𝔪
    exact iInf_le _ φ
  · exact le_iInf fun φ ↦ @nilradical_le_prime _ _ _ (RingHom.ker_isPrime φ)
