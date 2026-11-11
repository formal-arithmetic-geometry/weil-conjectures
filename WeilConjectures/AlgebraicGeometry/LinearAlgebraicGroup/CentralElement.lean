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

For a semisimple represented degree datum over an algebraically closed field of characteristic
zero there is a positive central pair `(N, z)`: `z = h Fᴺ` with `h ∈ H(k)` is central in `G(k)`
(`AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.exists_isPositiveCentralPair`). Along every
polynomial homomorphism `r : GL n k →* GL m k`, such as those building the tensor constructions
from duals, direct sums, tensor products and exterior powers, the pair is transported to the
positive central pair `(N, r z)` of `r ∘ ρ`
(`AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.IsPositiveCentralPair.map`), so `r z`
preserves every `W`-stable subspace and, by Schur's lemma, acts by a scalar on every simple
subquotient.

## Main statements

* `AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.exists_isPositiveCentralPair_and_map`:
  blueprint `proposition-central-element-arithmetic-monodromy-group`.
-/

@[expose] public section

open scoped Matrix
open Matrix.GeneralLinearGroup

namespace AlgebraicGeometry.Monodromy.RepresentedDegreeDatum

universe u v

variable {W : Type*} [Group W] {n k : Type u} [Fintype n] [DecidableEq n] [Field k]
  [IsAlgClosed k] [CharZero k] (D : RepresentedDegreeDatum W n k)

/-- **A central element of the arithmetic monodromy group** (blueprint:
`proposition-central-element-arithmetic-monodromy-group`). Let `D` be a semisimple represented
degree datum over an algebraically closed field `k` of characteristic zero, with monodromy
groups `H ⊆ G` and Frobenius `F = ρ(s)`. There are `N > 0` and `z = h Fᴺ ∈ Z(G)(k)` with
`h ∈ H(k)` (a positive central pair,
`proposition-central-element-arithmetic-monodromy-group--1`) such that, for every homomorphism
`r : GL n k →* GL m k` given by a `k`-algebra map `φ` of coordinate rings, `(N, r z)` is a
positive central pair of `r ∘ ρ`, `r z` preserves every `W`-stable subspace of `kᵐ`, and `r z` acts
by a scalar on every simple subquotient `S / U`
(`proposition-central-element-arithmetic-monodromy-group--2`). Every tensor construction on `kⁿ`
is a `W`-stable subquotient of such an `r ∘ ρ`, on which `z` acts through `r z`. -/
theorem exists_isPositiveCentralPair_and_map (hD : D.IsSemisimple) :
    ∃ (N : ℕ) (z : GL n k), D.IsPositiveCentralPair N z ∧
      ∀ {m : Type v} [Fintype m] [DecidableEq m] (r : GL n k →* GL m k)
        (φ : CoordinateRing m k →ₐ[k] CoordinateRing n k),
        (∀ g : GL n k, (evalAlgHom g).comp φ = evalAlgHom (r g)) →
        (D.map r).IsPositiveCentralPair N (r z) ∧
        (∀ (S : Subrepresentation (D.map r).asRepresentation) (x : m → k), x ∈ S →
          (r z : Matrix m m k) *ᵥ x ∈ S) ∧
        ∀ {U S : Subrepresentation (D.map r).asRepresentation},
          (S.subquotient U).IsIrreducible →
          ∃ c : k, ∀ x ∈ S, (r z : Matrix m m k) *ᵥ x - c • x ∈ U := by
  obtain ⟨N, z, hz⟩ := D.exists_isPositiveCentralPair hD
  refine ⟨N, z, hz, fun r φ hφ ↦ ?_⟩
  have hrz := hz.map r φ hφ
  have hzG := hrz.mem_zeroLocus_arithmeticMonodromy
  refine ⟨hrz, fun S x hx ↦ (D.map r).mulVec_mem_of_mem_zeroLocus_arithmeticMonodromy hzG S hx,
    fun {U S} hirr ↦ ?_⟩
  simpa using Subrepresentation.exists_apply_sub_smul_mem_of_isIrreducible hirr
    (Matrix.toLinAlgEquiv' (r z : Matrix _ _ k))
    (fun w x ↦ by
      simp only [asRepresentation, MonoidHom.coe_mk, OneHom.coe_mk,
        Matrix.toLinAlgEquiv'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, hrz.commute w])
    (fun x hx ↦ (D.map r).mulVec_mem_of_mem_zeroLocus_arithmeticMonodromy hzG U hx)
    (fun x hx ↦ (D.map r).mulVec_mem_of_mem_zeroLocus_arithmeticMonodromy hzG S hx)

end AlgebraicGeometry.Monodromy.RepresentedDegreeDatum
