/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Data.Set.Finite.Basic
public import WeilConjectures.GroupTheory.TateModule

/-!
# Tate modules

This file records the incarnation of the `ℓ`-adic Tate module `AddCommGroup.tateModule` (defined
in `WeilConjectures.GroupTheory.TateModule`) for the group of units of a field (the cyclotomic
Tate module `ℤ_ℓ(1)`), and the group-theoretic statement underlying the vanishing of the
Frobenius-fixed vectors of a Tate module.

The multiplicative group `μ_{ℓ^n}(K)` of `ℓ^n`-th roots of unity of a field is the `ℓ^n`-torsion
of `Kˣ`, so the cyclotomic Tate module is literally the Tate module of the additive group
`Additive Kˣ`; it is defined that way, so that the statements below apply to it.

## Main declarations

* `cyclotomicTateModule`: the cyclotomic Tate module `ℤ_ℓ(1)` of a field `K`, the Tate module of
  `Kˣ`.
* `AddCommGroup.eq_zero_of_mem_tateModule_of_forall_fixed`: an automorphism of an abelian group
  with finitely many fixed points fixes no nonzero vector of the Tate module.

## Blueprint

`cyclotomicTateModule` implements `sk-d-ab-cyclotomic`;
`AddCommGroup.eq_zero_of_mem_tateModule_of_forall_fixed` implements `sk-p-tate`.
-/

@[expose] public section

namespace AddCommGroup

/-- An automorphism of an abelian group whose fixed subgroup is finite fixes no nonzero element
of the Tate module.

This is the group-theoretic content of the statement that the geometric Frobenius `F` of an
abelian variety `A₀` over a finite field `k₀` has no nonzero fixed vector on the rational Tate
module `V_ℓ A`. It is equivalent to that statement: `T_ℓ M` is torsion-free, so it embeds into
`V_ℓ M = T_ℓ M[1/ℓ]`, and a `σ`-fixed vector of `V_ℓ M` becomes a `σ`-fixed vector of `T_ℓ M`
after clearing denominators. Moreover an automorphism and its inverse have the same fixed
vectors, so the arithmetic and the geometric Frobenius give the same statement. For
`M = A₀(k)` with `σ` the arithmetic Frobenius, the hypothesis `hfin` says that the fixed subgroup
`A^σ = A₀(k₀)` is finite, which is the only input the geometric proof uses.
(blueprint: `sk-p-tate`) -/
theorem eq_zero_of_mem_tateModule_of_forall_fixed {l : ℕ} [Fact l.Prime] {M : Type*}
    [AddCommGroup M] (s : M ≃+ M) (hfin : {x : M | s x = x}.Finite) {t : ℕ → M}
    (ht : t ∈ tateModule l M) (hst : ∀ n, s (t n) = t n) : t = 0 := by
  -- The fixed subgroup `M^σ` is finite; let `N` be its order.
  let H : AddSubgroup M := AddMonoidHom.eqLocus s.toAddMonoidHom (AddMonoidHom.id M)
  have : Finite H := hfin.to_subtype
  set N := Nat.card H
  have hN : 0 < N := Nat.card_pos
  let t' : tateModule l M := ⟨t, ht⟩
  funext n
  -- The coordinate `t (n + N)` is killed by `ℓ ^ (n + N)` and lies in `M^σ`, so its order is a
  -- power `ℓ ^ j` of `ℓ` dividing `N`; then `j < ℓ ^ j ≤ N`.
  have hx : t (n + N) ∈ H := hst (n + N)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : l.Prime)).mp <|
    addOrderOf_dvd_of_nsmul_eq_zero (x := t (n + N)) (n := l ^ (n + N)) <| by
      have := tateModule.pow_zsmul_coe t' (n + N)
      exact_mod_cast this
  have hjN : l ^ j ∣ N := by
    rw [← hj, ← AddSubgroup.addOrderOf_mk _ hx]
    exact addOrderOf_dvd_natCard _
  have hjle : j ≤ N :=
    ((Nat.lt_pow_self (Fact.out : l.Prime).one_lt).trans_le (Nat.le_of_dvd hN hjN)).le
  -- Hence `t n = ℓ ^ N • t (n + N) = 0`.
  have hkill : l ^ N • t (n + N) = 0 := by
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, hj]
    exact pow_dvd_pow l hjle
  calc t n = (l : ℤ) ^ N • t (n + N) := (tateModule.pow_zsmul_coe_add t' n N).symm
    _ = 0 := by exact_mod_cast hkill

end AddCommGroup

/-- The cyclotomic Tate module `ℤ_ℓ(1)` of a field `K` (only the multiplicative monoid of `K` is
used). The group
`μ_{ℓ^n}(K) = {u ∈ Kˣ : u ^ ℓ ^ n = 1}` of `ℓ^n`-th roots of unity forms an inverse system under
the `ℓ`-th power maps, and `ℤ_ℓ(1)` is the group of compatible systems `(u n)` with
`u n ∈ μ_{ℓ^n}(K)` and `u (n + 1) ^ ℓ = u n`: that is, the Tate module of the abelian group
`Kˣ`, written additively. The rational cyclotomic Tate module `ℚ_ℓ(1)` is the localisation
`ℤ_ℓ(1)[1/ℓ]`; it is not defined separately here.
(blueprint: `sk-d-ab-cyclotomic`) -/
def cyclotomicTateModule (K : Type*) [CommMonoid K] (l : ℕ) [Fact l.Prime] :
    AddSubgroup (ℕ → Additive Kˣ) :=
  AddCommGroup.tateModule l (Additive Kˣ)
