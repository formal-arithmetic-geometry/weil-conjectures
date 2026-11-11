/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy
public import WeilConjectures.Mathlib.RepresentationTheory.Subrepresentation

/-!
# A central element of the arithmetic monodromy group

For a semisimple represented degree datum `ρ : W → GL n k` over an algebraically closed field of
characteristic zero, with arithmetic and geometric monodromy groups `H ⊆ G`, there is a positive
central pair `(N, z)`: `z = h Fᴺ` with `h ∈ H(k)`, `F = ρ(γ)` and `z` central in `G(k)`
(`AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.exists_isPositiveCentralPair`). This file
combines it with the transport of positive central pairs along polynomial homomorphisms
`r : GL n k →* GL m k`
(`AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.IsPositiveCentralPair.map`)
and Schur's lemma (`Subrepresentation.exists_apply_sub_smul_mem_of_isIrreducible`): on every
representation `r ∘ ρ`, from which tensor constructions on `k^n` are cut out as subquotients,
`r(z)` preserves every `W`-stable subspace and acts on every simple subquotient by a scalar.

## Main statements

- `AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.exists_isPositiveCentralPair_and_forall_map`:
  blueprint `proposition-central-element-arithmetic-monodromy-group`.
-/

@[expose] public section

open scoped Matrix
open Matrix.GeneralLinearGroup

namespace AlgebraicGeometry.Monodromy.RepresentedDegreeDatum

universe u v

variable {W : Type*} [Group W] {n k : Type u} [Fintype n] [DecidableEq n] [Field k]
  (D : RepresentedDegreeDatum W n k) [IsAlgClosed k] [CharZero k]

/-- **A central element of the arithmetic monodromy group** (blueprint:
`proposition-central-element-arithmetic-monodromy-group`). Let `ρ : W → GL n k` be a semisimple
represented degree datum over an algebraically closed field of characteristic zero, with
monodromy groups `H ⊆ G` and `F = ρ(γ)`. There are `N > 0` and `z ∈ Z(G(k)) ∩ H(k) Fᴺ` such that,
for every homomorphism `r : GL n k →* GL m k` given by a `k`-algebra map `φ` of coordinate rings
(which is how a tensor construction on `k^n` arises), the element `r(z)` preserves every
`W`-stable subspace of `k^m` and acts by a scalar on every simple subquotient `S / (S ∩ U)`.

For semisimple Weil representations `V₁, …, Vₙ` this is applied to the Weil group `W(U₀)`,
`k = ℚ̄_ℓ` and `V = ⨁ Vᵢ`. -/
theorem exists_isPositiveCentralPair_and_forall_map (hD : D.IsSemisimple) :
    ∃ (N : ℕ) (z : GL n k), D.IsPositiveCentralPair N z ∧
      ∀ {m : Type v} [Fintype m] [DecidableEq m] (r : GL n k →* GL m k)
        (φ : CoordinateRing m k →ₐ[k] CoordinateRing n k),
        (∀ g : GL n k, (evalAlgHom g).comp φ = evalAlgHom (r g)) →
        (∀ S : Subrepresentation (D.map r).asRepresentation, ∀ x ∈ S,
          (r z : Matrix m m k) *ᵥ x ∈ S) ∧
        ∀ U S : Subrepresentation (D.map r).asRepresentation, (S.subquotient U).IsIrreducible →
          ∃ c : k, ∀ x ∈ S, (r z : Matrix m m k) *ᵥ x - c • x ∈ U := by
  obtain ⟨N, z, hz⟩ := D.exists_isPositiveCentralPair hD
  refine ⟨N, z, hz, fun r φ hφ ↦ ?_⟩
  have hz' := hz.map r φ hφ
  have hzG := hz'.mem_zeroLocus_arithmeticMonodromy
  refine ⟨fun S x hx ↦ (D.map r).mulVec_mem_of_mem_zeroLocus_arithmeticMonodromy hzG S hx,
    fun U S hirr ↦ ?_⟩
  exact Subrepresentation.exists_apply_sub_smul_mem_of_isIrreducible hirr
    (Matrix.toLinAlgEquiv' (r z : Matrix _ _ k))
    (fun w x ↦ by
      simp only [asRepresentation, MonoidHom.coe_mk, OneHom.coe_mk,
        Matrix.toLinAlgEquiv'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, hz'.commute w])
    (fun x hx ↦ (D.map r).mulVec_mem_of_mem_zeroLocus_arithmeticMonodromy hzG U hx)
    (fun x hx ↦ (D.map r).mulVec_mem_of_mem_zeroLocus_arithmeticMonodromy hzG S hx)

end AlgebraicGeometry.Monodromy.RepresentedDegreeDatum
