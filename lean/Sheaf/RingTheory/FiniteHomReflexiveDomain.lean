/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q136
-/

module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.RingTheory.FiniteInjectionBidualInjective

/-!
# Hom into a finite reflexive module over a Noetherian domain

Source: Stacks Project, Tag 0AV3 (`more-algebra-lemma-dual-reflexive`)
(blueprint: lem-sfb-finite-hom-reflexive-domain).
-/

@[expose] public section

universe u v w

namespace Module

/-- If `M` and `N` are finite modules over a commutative Noetherian domain and `N` is
reflexive, then `M →ₗ[R] N`, with its pointwise module structure, is reflexive.
Here `Module.Dual R T = T →ₗ[R] R`, and `Module.IsReflexive R T` means bijectivity
of the evaluation map `Module.Dual.eval R T`, sending `t` to `fun λ ↦ λ t`.

Source: Stacks Project, Tag 0AV3 (`more-algebra-lemma-dual-reflexive`)
(blueprint: lem-sfb-finite-hom-reflexive-domain).

Proof plan:
1. By `lem-sc-noetherian-finite-module-finite-presentation`, `M` is finitely presented.
   Using `def-sc-finitely-presented-module`, choose an exact presentation
   `R^m → R^n → M → 0`, with maps `a` and `b`. Put `H = Hom_R(M,N)`, `P = N^n`,
   and `Q = N^m`. Define `i(f)_j = f(b(e_j))` and
   `d(y)_k = ∑ j, a_{jk} • y_j`; these formulas give linear maps `i : H → P`, `d : P → Q`.
2. Each finite power `B = N^r` is reflexive: every functional on `B` is the sum
   of its coordinate functionals. For `x` in the double dual, set
   `x_j(λ) = x(λ ∘ π_j)` and use reflexivity of `N` to obtain the unique `y_j`
   evaluating to `x_j`. Expanding a functional by coordinates gives `e_B(y) = x`.
   Testing coordinate functionals proves injectivity of `e_B`. This includes `r = 0`.
   A finite generating set of `N` in each coordinate also makes `P` and `Q` finite.
3. The generators `b(e_j)` show that `i` is injective, and `b ∘ a = 0` gives `d ∘ i = 0`.
   If `d(y) = 0`, the map `g(v) = ∑ j, v_j • y_j` vanishes on the image of `a`,
   which is the kernel of `b`. Thus `f(b(v)) = g(v)` is well-defined and linear,
   and `i(f) = y`. Hence the image of `i` is the kernel of `d`.
   By `lem-weil-pbc-noetherian-submodule-finite`, this kernel is finite, so `H` is finite.
4. By `lem-per-finite-injection-bidual-injective`, the map `i**` is injective.
   Given `x` in `H**`, choose `p` with `e_P(p) = i**(x)`. For every `λ` in `Q*`,
   `e_Q(d(p))(λ) = e_P(p)(λ ∘ d) = x(λ ∘ d ∘ i) = 0`. Injectivity of `e_Q`
   gives `d(p) = 0`, so `p = i(h)` for some `h`. Naturality of evaluation gives
   `i**(e_H(h)) = e_P(i(h)) = i**(x)`; injectivity of `i**` gives `e_H(h) = x`.
   If `e_H(h) = 0`, then `e_P(i(h)) = 0`, so injectivity of `e_P` and `i` gives `h = 0`.
   Thus `e_H` is bijective; its inverse is linear since `e_H` is linear.
-/
theorem isReflexive_linearMap_of_finite_of_isNoetherianRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.IsReflexive R N] : Module.IsReflexive R (M →ₗ[R] N) := by
  sorry

end Module
