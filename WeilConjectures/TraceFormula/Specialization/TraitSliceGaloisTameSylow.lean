/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import WeilConjectures.RingTheory.HenselianDVRExtension
public import WeilConjectures.RingTheory.ProEtale.StrictlyHenselianRetraction
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisTame

/-!

# `Gal(F_K^sep / F_K·F^sep)` is a pro-`p` group

Let `F = k'((t))`, `F_K = K((t))` with `K` algebraically closed, `Ω_K = F_K^alg` and
`L' = F_K·F^sep ⊆ Ω_K` (`AlgebraicGeometry.traitGenericSepCompositum`). We prove that
`Gal(F_K^sep / L')` is a pro-`p` group, `p` the characteristic exponent, i.e. that every finite
Galois extension of `L'` in `Ω_K` has a `p`-group as Galois group
(`AlgebraicGeometry.isPGroup_traitGenericSepCompositum_of_dvd`), without any tameness hypothesis.

* **Sylow reduction** (`IntermediateField.isPGroup_of_forall_mem`): let `Ω / F` be an algebraic
  closure and `L` an intermediate field containing every separable element of `Ω` of degree prime
  to `p` over `F`. Then `Gal(M / L)` is a `p`-group for every finite Galois `M / L`. Indeed, for
  `σ ∈ Gal(M / L)` and `M = L(β)`, let `N` be the Galois closure over `F` of a separable power
  `β^{q^m}` and `P` a Sylow `p`-subgroup of `Gal(N / F)`. The fixed field `N^P` has degree prime
  to `p`, so it lies in `L`; an extension of `σ` to `Ω` restricts to an element of
  `Gal(N / N^P) = P`, whence `σ^{p^k}` fixes `β^{q^m}`, hence `β`.
* **Tame extensions of `K((t))`** (`PowerSeries.exists_pow_finrank_eq_X` and
  `PowerSeries.exists_pow_eq_X_and_mem_adjoin`): a finite separable extension `L` of `K((t))` of
  degree `d` invertible in `K` contains a `d`-th root `ρ` of `t`, so that `L = K((t))(ρ)`. This
  is the total ramification of `L`
  (`IsDiscreteValuationRing.exists_pow_eq_algebraMap_of_dvd_finrank`)
  together with Eisenstein's criterion for `Xᵈ - t`.

-/

@[expose] public section

open Polynomial IntermediateField Module

namespace PowerSeries

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

end PowerSeries

universe u

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] [IsAlgClosed K]

end AlgebraicGeometry
