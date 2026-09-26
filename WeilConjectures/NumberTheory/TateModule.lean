/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Tate modules

This file records the `ℓ`-adic Tate module of an abelian group, its multiplicative incarnation
for the group of units of a field (the cyclotomic Tate module `ℤ_ℓ(1)`), and the group-theoretic
statement underlying the vanishing of the Frobenius-fixed vectors of a Tate module.

## Main declarations

* `tateModule`: the `ℓ`-adic Tate module `T_ℓ M` of an abelian group `M`, as the subgroup of
  sequences `(t n)` with `ℓ ^ (n + 1) • t n = 0` and `ℓ • t (n + 1) = t n`.
* `cyclotomicTateModule`: the cyclotomic Tate module `ℤ_ℓ(1)` of a field `K`, the Tate module of
  `Kˣ` written multiplicatively.
* `tateModule_eq_zero_of_finite_fixedPoints`: an automorphism of an abelian group with finitely
  many fixed points fixes no nonzero vector of the Tate module.
-/

@[expose] public section

-- TODO(unify): sk-d-ab-tate
/-- The `ℓ`-adic Tate module of an abelian group `M`: systems `(t n)` with `ℓ ^ (n+1) • t n = 0`
and `ℓ • t (n + 1) = t n`. -/
def tateModule (l : ℕ) (M : Type*) [AddCommGroup M] : AddSubgroup (ℕ → M) where
  carrier := {t | ∀ n, (l ^ (n + 1)) • t n = 0 ∧ l • t (n + 1) = t n}
  zero_mem' n := by simp
  add_mem' {a b} ha hb n :=
    ⟨by simp [Pi.add_apply, nsmul_add, (ha n).1, (hb n).1],
      by simp [Pi.add_apply, nsmul_add, (ha n).2, (hb n).2]⟩
  neg_mem' {a} ha n :=
    ⟨by simp [Pi.neg_apply, (ha n).1], by simp [Pi.neg_apply, (ha n).2]⟩

/-- Blueprint `sk-d-ab-cyclotomic`: The cyclotomic Tate module. For a field `K` and a prime `ℓ`,
the group `μ_{ℓ^n}(K) = {u ∈ Kˣ : u ^ ℓ ^ n = 1}` of `ℓ^n`-th roots of unity forms an inverse
system under the `ℓ`-th power maps, and `ℤ_ℓ(1)` is the group of compatible systems
`(u n)` with `u n ∈ μ_{ℓ^{n+1}}(K)` and `u (n + 1) ^ ℓ = u n`. This is exactly the Tate module
of the abelian group `Kˣ`, written multiplicatively. The rational cyclotomic Tate module
`ℚ_ℓ(1)` is the localisation `ℤ_ℓ(1)[1/ℓ]`; it is not defined separately here. -/
def cyclotomicTateModule (l : ℕ) (K : Type*) [Field K] : Subgroup (ℕ → Kˣ) where
  carrier := {u | ∀ n, u n ^ l ^ (n + 1) = 1 ∧ u (n + 1) ^ l = u n}
  one_mem' n := by simp
  mul_mem' {a b} ha hb n :=
    ⟨by rw [Pi.mul_apply, mul_pow, (ha n).1, (hb n).1, one_mul],
      by rw [Pi.mul_apply, Pi.mul_apply, mul_pow, (ha n).2, (hb n).2]⟩
  inv_mem' {a} ha n :=
    ⟨by rw [Pi.inv_apply, inv_pow, (ha n).1, inv_one],
      by rw [Pi.inv_apply, Pi.inv_apply, inv_pow, (ha n).2]⟩

/-- Blueprint `sk-p-tate`: Tate modules and Frobenius. For an abelian variety `A₀` over a finite
field `k₀` with algebraic closure `k`, the geometric Frobenius `F` has no nonzero fixed vector on
the rational Tate module `V_ℓ A`. Abelian varieties are developed in a different part of the
blueprint, so only the group-theoretic content of the argument is recorded here: if `σ` is an
automorphism of an abelian group `M` whose fixed subgroup is finite, then `σ` fixes no nonzero
element of the Tate module `T_ℓ M`.

This is equivalent to the statement about `V_ℓ M`: the Tate module `T_ℓ M` is torsion-free, so it
embeds into `V_ℓ M = T_ℓ M[1/ℓ]`, and a `σ`-fixed vector of `V_ℓ M` becomes a `σ`-fixed vector of
`T_ℓ M` after clearing denominators; hence the fixed vectors of `T_ℓ M` vanish if and only if
`(V_ℓ M)^σ = 0`. Moreover an automorphism and its inverse have the same fixed vectors, so the
arithmetic and the geometric Frobenius give the same statement. For `M = A₀(k)` with `σ` the
arithmetic Frobenius, the hypothesis `hfin` says that the fixed subgroup `A^σ = A₀(k₀)` is
finite, which is the only input the geometric proof uses. -/
theorem tateModule_eq_zero_of_finite_fixedPoints {l : ℕ} (hl : l.Prime) {M : Type*}
    [AddCommGroup M] (s : M ≃+ M) (hfin : {x : M | s x = x}.Finite)
    {t : ℕ → M} (ht : t ∈ tateModule l M) (hst : ∀ n, s (t n) = t n) : t = 0 := by
  sorry
