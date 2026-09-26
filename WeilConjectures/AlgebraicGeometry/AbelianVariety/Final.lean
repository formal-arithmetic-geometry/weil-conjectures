/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion

/-!
# The abelian-variety estimate

The four clauses of the abelian-variety input to the curve estimates and the trace formula,
collected into a single theorem: multiplication by `n` is an isogeny of degree `n ^ (2 * g)`,
its kernel is finite flat and is étale away from the characteristic, the group of `n`-torsion
points over an algebraically closed field is `(ℤ/nℤ) ^ (2 * g)` and does not change under
extension of algebraically closed fields, and the group of points is divisible with `ℓ`-adic
Tate module free of rank `2 * g`.

## Main statements

- `AlgebraicGeometry.abelianVariety_estimate`: the abelian-variety estimate.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `sk-thm-av-final`: Abelian-variety estimate.

Let `A` be an abelian variety of dimension `g` over a field `K`, let `p = char K` and let
`n ≥ 1`.

* **(a)** `[n] : A ⟶ A` is a finite flat surjective homomorphism, hence an isogeny of degree
  `n ^ (2 * g)`; `A[n] = ker [n]` is a finite flat group scheme over `K` of order `n ^ (2 * g)`.
* **(b)** If `n` is prime to `p` (in particular if `p = 0`), then `A[n]` is finite étale of rank
  `n ^ (2 * g)`; for `p > 0` and `n = p ^ e` clause (a) already gives that `A[p ^ e]` is finite
  flat of order `p ^ (2 * g * e)`.
* **(c)** Let `K` be algebraically closed and `n` prime to `p`. Then
  `A(K)[n] ≅ (ℤ/nℤ) ^ (2 * g)`, and for every extension `K ⊆ K'` of algebraically closed fields
  the canonical map `A[n](K) ⟶ A[n](K')` is an isomorphism.
* **(d)** Let `K` be algebraically closed. Then `A(K)` is a divisible abelian group,
  `A(K)[n] ≅ (ℤ/nℤ) ^ (2 * g)` for every `n` prime to `p`, and for every prime `ℓ ≠ p` one has
  `T_ℓ A ≅ ℤ_[ℓ] ^ (2 * g)` and `V_ℓ A ≅ ℚ_[ℓ] ^ (2 * g)`. -/
theorem abelianVariety_estimate (p : ℕ) [CharP K p] (A : Over (Spec (.of K))) [GrpObj A]
    [IsCommMonObj A] [IsAbelianVariety A] (g : ℕ)
    (hg : topologicalKrullDim A.left = (g : ℕ∞)) :
    (∀ n : ℕ, 1 ≤ n →
        IsIsogeny (𝟙 A ^ n) ∧ Flat (𝟙 A ^ n).left ∧ isogenyDegree (𝟙 A ^ n) = n ^ (2 * g) ∧
          IsFinite (torsionSubgroupScheme A n).hom ∧ Flat (torsionSubgroupScheme A n).hom ∧
          (torsionSubgroupScheme A n).hom.finrankΓ = n ^ (2 * g)) ∧
      (∀ n : ℕ, 1 ≤ n → (p = 0 ∨ ¬ p ∣ n) → Etale (torsionSubgroupScheme A n).hom) ∧
      (IsAlgClosed K → ∀ n : ℕ, 1 ≤ n → (p = 0 ∨ ¬ p ∣ n) →
        Nonempty (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of K))) ⟶ A)) (n : ℤ) ≃+
            (Fin (2 * g) → ZMod n)) ∧
          ∀ (K' : Type u) [Field K'] [Algebra K K'], IsAlgClosed K' →
            Function.Bijective
              (fun s : 𝟙_ (Over (Spec (.of K))) ⟶ torsionSubgroupScheme A n =>
                toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ≫ s)) ∧
      (IsAlgClosed K →
        (∀ n : ℕ, 1 ≤ n → Function.Surjective fun a : 𝟙_ (Over (Spec (.of K))) ⟶ A => a ^ n) ∧
          ∀ (l : ℕ) (_ : Fact l.Prime), l ≠ p →
            Nonempty (tateModule l A ≃ₗ[ℤ_[l]] (Fin (2 * g) → ℤ_[l])) ∧
              Nonempty (rationalTateModule l A ≃ₗ[ℚ_[l]] (Fin (2 * g) → ℚ_[l]))) :=
  sorry

end AlgebraicGeometry
