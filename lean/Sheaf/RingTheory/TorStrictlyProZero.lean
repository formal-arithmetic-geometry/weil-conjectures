/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Module.ULift
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-! # Tor against ideal-power quotients is strictly pro-zero

Source: Stacks Project, More on Algebra, Lemma Tag 0911 (lemma-tor-strictly-pro-zero)
(blueprint: lem-weil-pbc-tor-strictly-pro-zero).
-/

universe u v

open CategoryTheory

namespace ModuleCat

/-- For a finite module over a Noetherian ring, each positive-degree Tor system against
ideal-power quotients has uniformly vanishing sufficiently long transition maps.
Source: Stacks Project, More on Algebra, Lemma Tag 0911 (lemma-tor-strictly-pro-zero)
(blueprint: lem-weil-pbc-tor-strictly-pro-zero).

The lifts only place the two modules in the same universe. `Submodule.factor` is the
canonical quotient reduction, conjugated by `ULift.moduleEquiv`; `Tor'` derives in the
first variable, as in def-weil-pbc-tor-modules. Ideal powers include `I ^ 0 = ⊤`.

Proof, following the five steps of the node:
1. Choose a finite free resolution of `M` by
   lem-weil-pbc-finite-free-resolution-noetherian. Its first kernel `K` is finite,
   and shifting the resolution gives a free resolution of `K`.
2. For degree `p ≥ 2`, the complexes computing Tor of `M` in degree `p` and Tor
   of `K` in degree `p - 1` have identical terms and differentials around that degree.
   This gives dimension shifting, natural in the second module
   (def-weil-pbc-tor-modules).
3. Using lem-weil-pbc-tensor-over-quotient-ring and lem-weil-pbc-tensor-right-exact,
   identify Tor₁ of `M` against `A/J` with `(K ∩ J Aᵗ)/JK`. For `J ≤ J'`, the
   transition sends the class of `k` modulo `JK` to its class modulo `J'K`.
4. Apply lem-weil-pbc-artin-rees to `K ⊆ Aᵗ`. It gives `c₀` with
   `K ∩ Iⁿ Aᵗ ⊆ I^(n-c) K` for all `n ≥ c ≥ c₀`. Take `c = max c₀ 1`.
   The reduction from degree `n` to `n-c` therefore kills every Tor₁ class.
5. Induct on positive `p`, applying the inductive claim to the finite module `K`.
   The natural dimension-shifting isomorphisms transfer its vanishing transitions
   to Tor of `M`, with the same positive constant. -/
theorem tor_quotient_pow_strictly_pro_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : ℕ) (hp : 0 < p) :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, c ≤ n →
      ((Tor' (ModuleCat (ULift.{v} A)) p).obj
        (ModuleCat.of (ULift.{v} A) (ULift.{u} M))).map
        (ModuleCat.ofHom
          (((ULift.moduleEquiv : ULift.{v} (A ⧸ I ^ (n - c)) ≃ₗ[ULift.{v} A]
              A ⧸ I ^ (n - c)).symm.toLinearMap).comp
            (((Submodule.factor (Ideal.pow_le_pow_right (Nat.sub_le n c)) :
              (A ⧸ I ^ n) →ₗ[A] (A ⧸ I ^ (n - c))).restrictScalars (ULift.{v} A)).comp
              (ULift.moduleEquiv : ULift.{v} (A ⧸ I ^ n) ≃ₗ[ULift.{v} A]
                A ⧸ I ^ n).toLinearMap))) = 0 := by
  sorry

end ModuleCat
