/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-! # Normalization and residue quotient of equal-constant pairs

Source: Stacks Project, curves.tex, Tag 0C4A (lemma-2-branches-delta-1), Case I
and the subsequent by-hand delta calculation
(blueprint: lem-trf-equal-constant-normalization-residue-quotient).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace RingTheory

/-- The equal-constant subring has product normalization and a one-dimensional residue
quotient. Since `S` is already stable under its own scalar action, its `S`-span
has carrier exactly `S` and gives the submodule in the additive quotient `P/S`.
The integral-closure clause uses `RingHom.IsIntegralElem`, the monic-polynomial
predicate defining `IsIntegral` and hence `integralClosure`, along the actual embedding.
The specified actions and representative formulas determine all maps canonically.

Source: Stacks Project, curves.tex, Tag 0C4A (lemma-2-branches-delta-1), Case I
and the subsequent by-hand delta calculation
(blueprint: lem-trf-equal-constant-normalization-residue-quotient).

Proof:
1. For p=(f,g), put a=f(0)-g(0), s=(f-C(a),g) and t=(C(a),C(a)). Then
   s,t belong to S and p=s+t*(1,0). The idempotent epsilon=(1,0) satisfies
   epsilon^2=epsilon, so P=S+S*epsilon=S[epsilon]. The monic polynomial
   (T-s)(T-s-t) kills p, proving integrality over S.
2. Project a monic equation for a Laurent pair to each coordinate. If a nonzero
   coordinate has negative lowest exponent n, the leading term of its Nth power
   occurs at N*n with nonzero coefficient. Every lower power multiplied by a
   power-series coefficient has all exponents strictly greater than N*n. This
   contradicts the equation. Thus both coordinates are power series, giving
   precisely P as integral closure in the Laurent product.
3. Constant evaluation c on S is a surjective ring homomorphism, split by diagonal
   constants. Its kernel m consists of the pairs with both constants zero. By
   lem-weil-pbc-power-series-local-ring, a pair with nonzero common constant has
   componentwise inverses with equal constants. Conversely a pair in m cannot be
   a unit. Every proper ideal is therefore contained in m, which is the unique
   maximal ideal, and the induced map S/m to k is a ring isomorphism.
4. The difference d of the two constant coefficients is additive and satisfies
   d(s*p)=c(s)*d(p). It is onto via a mapping to (C(a),0), and its kernel is S.
   It descends to the displayed S-linear equivalence P/S to k. Its inverse sends
   a to the class of (C(a),0): p-(C(d(p)),0) belongs to S. Elements of m act as
   zero on the quotient. Thus the S-action descends to S/m, and the class of
   epsilon, whose difference is 1, is its one-element basis. All formulas hold
   in every characteristic, including characteristic two. -/
theorem equalConstant_normalization_residue_quotient
    (k : Type u) [Field k] (S : Subring (PowerSeries k × PowerSeries k))
    (hS : ∀ p : PowerSeries k × PowerSeries k,
      p ∈ S ↔ PowerSeries.constantCoeff p.1 = PowerSeries.constantCoeff p.2) :
    (∀ z : LaurentSeries k × LaurentSeries k,
      ((RingHom.prodMap (HahnSeries.ofPowerSeries ℤ k)
        (HahnSeries.ofPowerSeries ℤ k)).comp S.subtype).IsIntegralElem z ↔
      z ∈ (⊤ : Subring (PowerSeries k × PowerSeries k)).map
        (RingHom.prodMap (HahnSeries.ofPowerSeries ℤ k)
          (HahnSeries.ofPowerSeries ℤ k))) ∧
    (∀ p : PowerSeries k × PowerSeries k, ∃ s t : S,
      p = s.val + t.val * (1, 0)) ∧
    Algebra.adjoin S ({(1, 0)} : Set (PowerSeries k × PowerSeries k)) = ⊤ ∧
    ((1, 0) : PowerSeries k × PowerSeries k) ^ 2 = (1, 0) ∧
    IsLocalRing S ∧
    ∃ (m : Ideal S) (c : S →+* k),
      (∀ s : S, s ∈ m ↔
        PowerSeries.constantCoeff s.val.1 = 0 ∧ PowerSeries.constantCoeff s.val.2 = 0) ∧
      m.IsMaximal ∧ (∀ I : Ideal S, I.IsMaximal → I = m) ∧
      (∀ s : S, c s = PowerSeries.constantCoeff s.val.1 ∧
        c s = PowerSeries.constantCoeff s.val.2) ∧
      Function.Surjective c ∧ RingHom.ker c = m ∧
      (∃ ρ : (S ⧸ m) ≃+* k, ∀ s : S, ρ (Ideal.Quotient.mk m s) = c s) ∧
      ∃ (_ : Module S k),
        (∀ (s : S) (a : k), s • a = c s * a) ∧
        ∃ d : (PowerSeries k × PowerSeries k) →ₗ[S] k,
          (∀ p : PowerSeries k × PowerSeries k,
            d p = PowerSeries.constantCoeff p.1 - PowerSeries.constantCoeff p.2) ∧
          Function.Surjective d ∧
          LinearMap.ker d = Submodule.span S (S : Set (PowerSeries k × PowerSeries k)) ∧
          (∃ e : ((PowerSeries k × PowerSeries k) ⧸
              Submodule.span S (S : Set (PowerSeries k × PowerSeries k))) ≃ₗ[S] k,
            ∀ p : PowerSeries k × PowerSeries k, e (Submodule.Quotient.mk p) = d p) ∧
          (∀ (s : S), s ∈ m → ∀ q : (PowerSeries k × PowerSeries k) ⧸
            Submodule.span S (S : Set (PowerSeries k × PowerSeries k)), s • q = 0) ∧
          ∃ (_ : Module (S ⧸ m) ((PowerSeries k × PowerSeries k) ⧸
              Submodule.span S (S : Set (PowerSeries k × PowerSeries k)))),
            (∀ (s : S) (q : (PowerSeries k × PowerSeries k) ⧸
                Submodule.span S (S : Set (PowerSeries k × PowerSeries k))),
              (Ideal.Quotient.mk m s) • q = s • q) ∧
            ∃ b : Module.Basis (Fin 1) (S ⧸ m) ((PowerSeries k × PowerSeries k) ⧸
                Submodule.span S (S : Set (PowerSeries k × PowerSeries k))),
              b 0 = Submodule.Quotient.mk ((1, 0) : PowerSeries k × PowerSeries k) := by
  sorry

end RingTheory
