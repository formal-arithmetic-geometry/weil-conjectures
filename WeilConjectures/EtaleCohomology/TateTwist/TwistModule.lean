/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The twist modules `P(m)`

Let `k` be a field, `Λ` a commutative ring and `n ≥ 1` an integer with `n Λ = 0`; in the
blueprint `Λ = 𝒪_E/ϖ^n` and `n = ℓ^N` for an *admissible* exponent `N`, i.e. one with
`ℓ^N Λ = 0`. The group `μ_n(k)` of `n`-th roots of unity of `k`, written additively, is a
`ℤ/n`-module, and

`P(1) = Λ ⊗_{ℤ/n} μ_n(k)`

is a `Λ`-module (`tateTwistModuleOne`). For `m ≥ 0` the module `P(m)` is the `m`-th tensor
power of `P(1)` over `Λ`, with `P(0) = ⨂^0 P(1) = Λ` (`tateTwistModuleZeroIso`), and for `m < 0`
it is the `Λ`-dual `Hom_Λ(P(-m), Λ)` (`tateTwistModule`).

These are the values of the constant sheaves `Λ_W(m)` on a scheme `W` over a separably closed
field `k`: there `μ_{n, W}` is the constant sheaf with value `μ_n(k)`.

## Implementation notes

The blueprint writes `P(1) = μ_n(k) ⊗_{ℤ/n} Λ`; here the factors are swapped, so that the
`Λ`-module structure is the one Mathlib puts on a tensor product through its left factor. The
`ℤ/n`-algebra structure of `Λ` is an instance argument: a ring has at most one, and it exists
exactly when `n Λ = 0` (`ZMod.algebra'`).

## Main definitions

- `tateTwistModuleOne`: the `Λ`-module `P(1) = Λ ⊗_{ℤ/n} μ_n(k)`.
- `tateTwistModule`: the `Λ`-modules `P(m)`, `m ∈ ℤ`.
-/

@[expose] public section

universe u v

open TensorProduct

variable (k : Type u) [Field k] (Λ : Type v) [CommRing Λ] (n : ℕ)

/-- The group `μ_n(k)` of `n`-th roots of unity, written additively, is a `ℤ/n`-module. -/
instance rootsOfUnity.instModuleZModAdditive :
    Module (ZMod n) (Additive (rootsOfUnity n k)) :=
  AddCommGroup.zmodModule fun x ↦ by
    change Additive.toMul (n • x) = 1
    rw [toMul_nsmul]
    exact Subtype.ext (by simpa using (mem_rootsOfUnity n _).1 x.toMul.2)

variable [Algebra (ZMod n) Λ]

/-- Blueprint `pur9-def-twist-module`: Admissible exponents and the twist modules

The `Λ`-module `P(1) = Λ ⊗_{ℤ/n} μ_n(k)`, for `n Λ = 0` (encoded by the `ℤ/n`-algebra structure
of `Λ`). For `Λ = 𝒪_E/ϖ^n` and `n = ℓ^N` with `N` admissible, i.e. `ℓ^N Λ = 0`, this is the
module `P_N(1) = μ_{ℓ^N}(k) ⊗_{ℤ/ℓ^N} 𝒪_E/ϖ^n` of the blueprint. -/
noncomputable def tateTwistModuleOne : ModuleCat.{max u v} Λ :=
  ModuleCat.of Λ (Λ ⊗[ZMod n] Additive (rootsOfUnity n k))

/-- Blueprint `pur9-def-twist-module`: Admissible exponents and the twist modules

The twist modules `P(m)`, `m ∈ ℤ`: for `m ≥ 0` the `m`-th tensor power over `Λ` of
`P(1) = Λ ⊗_{ℤ/n} μ_n(k)` (`tateTwistModuleOne`), so that `P(0) = Λ`
(`tateTwistModuleZeroIso`), and for `m < 0` the dual `Hom_Λ(P(-m), Λ)`. -/
noncomputable def tateTwistModule : ℤ → ModuleCat.{max u v} Λ
  | .ofNat m => ModuleCat.of Λ (⨂[Λ]^m (tateTwistModuleOne k Λ n))
  | .negSucc m => ModuleCat.of Λ (Module.Dual Λ (⨂[Λ]^(m + 1) (tateTwistModuleOne k Λ n)))

lemma tateTwistModule_natCast (m : ℕ) :
    tateTwistModule k Λ n m = ModuleCat.of Λ (⨂[Λ]^m (tateTwistModuleOne k Λ n)) :=
  rfl

lemma tateTwistModule_negSucc (m : ℕ) :
    tateTwistModule k Λ n (Int.negSucc m) =
      ModuleCat.of Λ (Module.Dual Λ (⨂[Λ]^(m + 1) (tateTwistModuleOne k Λ n))) :=
  rfl

lemma tateTwistModule_neg_natCast (m : ℕ) (hm : m ≠ 0) :
    tateTwistModule k Λ n (-m) =
      ModuleCat.of Λ (Module.Dual Λ (⨂[Λ]^m (tateTwistModuleOne k Λ n))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rfl

/-- `P(0) = ⨂^0 P(1)` is the free module `Λ` of rank one. -/
noncomputable def tateTwistModuleZeroIso :
    tateTwistModule k Λ n 0 ≅ ModuleCat.of Λ (ULift.{u} Λ) :=
  LinearEquiv.toModuleIso ((PiTensorProduct.isEmptyEquiv (Fin 0)).trans ULift.moduleEquiv.symm)

variable {k n} in
/-- If `ζ` is a primitive `n`-th root of unity of `k`, then `P(1)` is free of rank one, with
basis `1 ⊗ ζ`: `ζ` generates `μ_n(k) ≅ ℤ/n`, and `Λ ⊗_{ℤ/n} ℤ/n = Λ`. -/
noncomputable def tateTwistModuleOneIsoOfIsPrimitiveRoot [NeZero n] {ζ : kˣ}
    (hζ : IsPrimitiveRoot ζ n) :
    tateTwistModuleOne k Λ n ≅ ModuleCat.of Λ (ULift.{u} Λ) :=
  let e : ZMod n ≃+ Additive (rootsOfUnity n k) :=
    hζ.zmodEquivZPowers.trans (MulEquiv.subgroupCongr hζ.zpowers_eq).toAdditive
  let e' : ZMod n ≃ₗ[ZMod n] Additive (rootsOfUnity n k) :=
    LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap n) e.bijective
  LinearEquiv.toModuleIso ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Λ Λ)
      e'.symm).trans
    ((TensorProduct.AlgebraTensorModule.rid (ZMod n) Λ Λ).trans ULift.moduleEquiv.symm))
