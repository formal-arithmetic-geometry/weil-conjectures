/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Data.Set.Finite.Basic

/-!
# Tate modules

This file records the `ℓ`-adic Tate module of an abelian group, its incarnation for the group of
units of a field (the cyclotomic Tate module `ℤ_ℓ(1)`), and the group-theoretic statement
underlying the vanishing of the Frobenius-fixed vectors of a Tate module.

The multiplicative group `μ_{ℓ^n}(K)` of `ℓ^n`-th roots of unity of a field is the `ℓ^n`-torsion
of `Kˣ`, so the cyclotomic Tate module is literally the Tate module of the additive group
`Additive Kˣ`; it is defined that way, so that the statements below apply to it.

## Main declarations

* `AddCommGroup.tateModule`: the `ℓ`-adic Tate module `T_ℓ M` of an abelian group `M`, as the
  subgroup of sequences `(t n)` with `ℓ ^ (n + 1) • t n = 0` and `ℓ • t (n + 1) = t n`.
* `cyclotomicTateModule`: the cyclotomic Tate module `ℤ_ℓ(1)` of a field `K`, the Tate module of
  `Kˣ`.
* `AddCommGroup.eq_zero_of_mem_tateModule_of_forall_fixed`: an automorphism of an abelian group
  with finitely many fixed points fixes no nonzero vector of the Tate module.

## Blueprint

`cyclotomicTateModule` implements `sk-d-ab-cyclotomic`;
`AddCommGroup.eq_zero_of_mem_tateModule_of_forall_fixed` implements `sk-p-tate`.

## TODO

* `AddCommGroup.tateModule` is the same construction as the Tate module of an abelian variety,
  `sk-d-ab-tate`, which the abelian-varieties block of the blueprint formalises in parallel. The
  two should be unified on a single definition — this one, in this file — before either block is
  proved, so that `sk-p-tate` is attached to the right object.
* `T_ℓ M` carries a `ℤ_[ℓ]`-module structure, coming from its description as an inverse limit of
  `ZMod (ℓ ^ n)`-modules; the rational Tate module `V_ℓ M = T_ℓ M[1/ℓ]` needs it. That structure
  is a construction rather than a statement, and belongs with the unification above.
-/

@[expose] public section

namespace AddCommGroup

/-- The `ℓ`-adic Tate module of an abelian group `M`: systems `(t n)` with `ℓ ^ (n + 1) • t n = 0`
and `ℓ • t (n + 1) = t n`. -/
def tateModule (l : ℕ) (M : Type*) [AddCommGroup M] : AddSubgroup (ℕ → M) where
  carrier := {t | ∀ n, (l ^ (n + 1)) • t n = 0 ∧ l • t (n + 1) = t n}
  zero_mem' n := by simp
  add_mem' {a b} ha hb n :=
    ⟨by simp [Pi.add_apply, nsmul_add, (ha n).1, (hb n).1],
      by simp [Pi.add_apply, nsmul_add, (ha n).2, (hb n).2]⟩
  neg_mem' {a} ha n :=
    ⟨by simp [Pi.neg_apply, (ha n).1], by simp [Pi.neg_apply, (ha n).2]⟩

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
theorem eq_zero_of_mem_tateModule_of_forall_fixed {l : ℕ} {M : Type*} [AddCommGroup M]
    (s : M ≃+ M) (hfin : {x : M | s x = x}.Finite) {t : ℕ → M} (ht : t ∈ tateModule l M)
    (hst : ∀ n, s (t n) = t n) : t = 0 := by
  sorry

end AddCommGroup

/-- The cyclotomic Tate module `ℤ_ℓ(1)` of a field `K` (only the multiplicative monoid of `K` is
used). The group
`μ_{ℓ^n}(K) = {u ∈ Kˣ : u ^ ℓ ^ n = 1}` of `ℓ^n`-th roots of unity forms an inverse system under
the `ℓ`-th power maps, and `ℤ_ℓ(1)` is the group of compatible systems `(u n)` with
`u n ∈ μ_{ℓ^{n+1}}(K)` and `u (n + 1) ^ ℓ = u n`: that is, the Tate module of the abelian group
`Kˣ`, written additively. The rational cyclotomic Tate module `ℚ_ℓ(1)` is the localisation
`ℤ_ℓ(1)[1/ℓ]`; it is not defined separately here.
(blueprint: `sk-d-ab-cyclotomic`) -/
def cyclotomicTateModule (K : Type*) [CommMonoid K] (l : ℕ) :
    AddSubgroup (ℕ → Additive Kˣ) :=
  AddCommGroup.tateModule l (Additive Kˣ)
