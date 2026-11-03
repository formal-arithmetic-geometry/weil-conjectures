/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Weights of finite-dimensional Frobenius modules

Source: the blueprint of the Weil conjectures, chapter `sec-purity-real-sheaves`,
section `sk-p-real-semi`, node `def-weil-frobenius-module-weights`, order 2651
(blueprint: def-weil-frobenius-module-weights).

The upstream `FrobeniusModule.IsPureOfWeight` declaration gives the purity
predicate.  This file gives the finite stable-filtration predicate for mixed
weights, using the induced automorphism on each successive quotient.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public section

universe u v

namespace FrobeniusModule

/--
A Frobenius module is mixed of weights at most `w` when it admits a finite
increasing Frobenius-stable filtration from zero to the whole module, and each
successive quotient carries the induced Frobenius and is pure of some weight
bounded by `w`. The image-membership witness in the quotient-action clause is
guaranteed by stability; quantifying over it avoids a local proof in the definition.

Source: Weil-conjectures blueprint, chapter `sec-purity-real-sheaves`, section
`sk-p-real-semi`, node `def-weil-frobenius-module-weights`, order 2651
(blueprint: def-weil-frobenius-module-weights).
-/
def IsMixedOfWeightsAtMost
    (p a ell : ℕ) [Fact (Nat.Prime p)] (_ha : 1 ≤ a)
    [Fact (Nat.Prime ell)] (_hellp : ell ≠ p) (Qlb : Type v) [Field Qlb]
    [Algebra (ℚ_[ell]) Qlb] (_hQ : IsAlgClosure (ℚ_[ell]) Qlb)
    (iota : Qlb ≃+* ℂ) (M : FrobeniusModule.{u, v} Qlb) (w : ℝ) : Prop :=
  ∃ (m : ℕ) (V : Fin (m + 1) → Submodule Qlb M.carrier)
    (_hzero : V 0 = ⊥)
    (_hwhole : V ⟨m, Nat.lt_succ_self m⟩ = ⊤)
    (_hincreasing : ∀ r : Fin m, V r.castSucc ≤ V r.succ)
    (_hstable : ∀ r : Fin (m + 1),
      Submodule.map M.frobenius.toLinearMap (V r) = V r),
    ∀ r : Fin m,
      ∃ (wr : ℝ)
        (G : (↥(V r.succ) ⧸
            ((V r.castSucc : Submodule Qlb M.carrier).comap (V r.succ).subtype)) ≃ₗ[Qlb]
          (↥(V r.succ) ⧸
            ((V r.castSucc : Submodule Qlb M.carrier).comap (V r.succ).subtype))),
        wr ≤ w ∧
        (∀ (x : V r.succ) (hx : M.frobenius (x : M.carrier) ∈ V r.succ),
          G (Submodule.Quotient.mk x) =
            Submodule.Quotient.mk ⟨M.frobenius x, hx⟩) ∧
        FrobeniusModule.IsPureOfWeight (iota : Qlb →+* ℂ) (p ^ a)
          { carrier := ↥(V r.succ) ⧸
              ((V r.castSucc : Submodule Qlb M.carrier).comap (V r.succ).subtype)
            frobenius := G } wr

end FrobeniusModule
