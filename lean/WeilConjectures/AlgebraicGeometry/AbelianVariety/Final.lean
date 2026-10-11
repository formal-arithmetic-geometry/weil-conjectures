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

The abelian-variety input to the curve estimates and the trace formula, collected from the
statements of this block: multiplication by `n` is an isogeny of degree `n ^ (2 * g)`, its
kernel is finite flat and is étale away from the characteristic, the group of `n`-torsion
points over an algebraically closed field is `(ℤ/nℤ) ^ (2 * g)` and does not change under
extension of algebraically closed fields, and the group of points is divisible with `ℓ`-adic
Tate module free of rank `2 * g`.

Each conjunct below is an instance of a single-conclusion statement proved elsewhere in the
block; the two theorems here only assemble them, splitting off the clauses that need an
algebraically closed base field, since `IsAlgClosed` is a class and is unusable as a plain
implication inside a conclusion.

## Main statements

- `AlgebraicGeometry.abelianVariety_estimate`: clauses (a) and (b) of the blueprint theorem,
  over an arbitrary field.
- `AlgebraicGeometry.abelianVariety_estimate_of_isAlgClosed`: clauses (c) and (d), over an
  algebraically closed field.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `sk-thm-av-final`: Abelian-variety estimate, clauses (a) and (b).

Let `A` be an abelian variety of dimension `g` over a field `K`, let `p = char K` and let
`0 < n`.

* **(a)** `[n] : A ⟶ A` is a finite flat surjective homomorphism, hence an isogeny of degree
  `n ^ (2 * g)`; `A[n] = ker [n]` is a finite flat group scheme over `K` of order `n ^ (2 * g)`.
* **(b)** If `n` is prime to `p` (in particular if `p = 0`), then `A[n]` is étale of rank
  `n ^ (2 * g)`; for `p > 0` and `n = p ^ e` clause (a) already gives that `A[p ^ e]` is finite
  flat of order `p ^ (2 * g * e)`. -/
theorem abelianVariety_estimate (p : ℕ) [CharP K p] (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] :
    (∀ n : ℕ, 0 < n → IsIsogeny (𝟙 A ^ n)) ∧
      (∀ n : ℕ, 0 < n → isogenyDegree (𝟙 A ^ n) = n ^ (2 * IsAbelianVariety.dim A)) ∧
      (∀ n : ℕ, 0 < n → IsFinite (torsionSubgroupScheme A n).hom) ∧
      (∀ n : ℕ, 0 < n → Flat (torsionSubgroupScheme A n).hom) ∧
      (∀ n : ℕ, 0 < n →
        (torsionSubgroupScheme A n).hom.finrankΓ = n ^ (2 * IsAbelianVariety.dim A)) ∧
      (∀ n : ℕ, 0 < n → ¬ p ∣ n → Etale (torsionSubgroupScheme A n).hom) :=
  ⟨isIsogeny_npow_id, isogenyDegree_npow_id, isFinite_torsionSubgroupScheme A,
    flat_torsionSubgroupScheme, finrankΓ_torsionSubgroupScheme,
    etale_torsionSubgroupScheme p A⟩

/-- Blueprint `sk-thm-av-final`: Abelian-variety estimate, clauses (c) and (d).

Let `A` be an abelian variety of dimension `g` over an algebraically closed field `K`, let
`p = char K` and let `0 < n`.

* **(c)** For `n` prime to `p` one has `A(K)[n] ≅ (ℤ/nℤ) ^ (2 * g)`, and for every extension
  `K ⊆ K'` of algebraically closed fields the canonical map `A[n](K) ⟶ A[n](K')` is a bijection.
* **(d)** `A(K)` is a divisible abelian group, and for every prime `ℓ ≠ p` one has
  `T_ℓ A ≅ ℤ_[ℓ] ^ (2 * g)` and `V_ℓ A ≅ ℚ_[ℓ] ^ (2 * g)`. -/
theorem abelianVariety_estimate_of_isAlgClosed [IsAlgClosed K] (p : ℕ) [CharP K p]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] :
    (∀ n : ℕ, 0 < n → ¬ p ∣ n →
        Nonempty (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of K))) ⟶ A)) (n : ℤ) ≃+
          (Fin (2 * IsAbelianVariety.dim A) → ZMod n))) ∧
      (∀ n : ℕ, 0 < n → ¬ p ∣ n → ∀ (K' : Type u) [Field K'] [Algebra K K'] [IsAlgClosed K'],
        Function.Bijective
          (fun s : 𝟙_ (Over (Spec (.of K))) ⟶ torsionSubgroupScheme A n ↦
            toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ≫ s)) ∧
      (∀ n : ℕ, 0 < n → Function.Surjective fun a : 𝟙_ (Over (Spec (.of K))) ⟶ A ↦ a ^ n) ∧
      (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
        Nonempty (IsAbelianVariety.tateModule ℓ A ≃ₗ[ℤ_[ℓ]]
          (Fin (2 * IsAbelianVariety.dim A) → ℤ_[ℓ]))) ∧
      (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
        Nonempty (IsAbelianVariety.rationalTateModule ℓ A ≃ₗ[ℚ_[ℓ]]
          (Fin (2 * IsAbelianVariety.dim A) → ℚ_[ℓ]))) :=
  ⟨nonempty_addEquiv_torsionBy p A, bijective_toUnit_comp_torsionSubgroupScheme p A,
    surjective_npow_points, fun ℓ _ hℓ ↦ IsAbelianVariety.nonempty_linearEquiv_tateModule ℓ A p hℓ,
    fun ℓ _ hℓ ↦ IsAbelianVariety.nonempty_linearEquiv_rationalTateModule ℓ A p hℓ⟩

end AlgebraicGeometry
