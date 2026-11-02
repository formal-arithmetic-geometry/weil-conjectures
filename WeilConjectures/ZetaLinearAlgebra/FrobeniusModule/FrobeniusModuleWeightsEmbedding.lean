/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.FrobeniusModuleWeights

/-! # Mixed weights for an arbitrary complex field embedding

Source: latest blueprint, sec-purity-real-sheaves/sk-p-real-semi,
def-weil-frobenius-module-weights; the finite stable filtration definition
(blueprint: def-weil-frobenius-module-weights).

This interface retains the recorded definition and supplies the same filtration
for a field embedding that need not be surjective, including lifted coefficient fields.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v

namespace FrobeniusModule

/-- A finite Frobenius-stable filtration with pure graded pieces of weights at most w.
The embedding is an arbitrary field homomorphism; there is no continuity or
surjectivity hypothesis. Quotient actions are the actions induced by Frobenius,
without any semisimplicity hypothesis. A filtration of length zero is allowed.

Source: latest blueprint, def-weil-frobenius-module-weights, displayed filtration
and quotient-action paragraph (blueprint: def-weil-frobenius-module-weights). -/
def IsMixedOfWeightsAtMostEmbedding {K : Type v} [Field K]
    (iota : K →+* ℂ) (q : ℕ) (M : FrobeniusModule.{u, v} K) (w : ℝ) : Prop :=
  ∃ (m : ℕ) (V : Fin (m + 1) → Submodule K M.carrier)
    (_hzero : V 0 = ⊥)
    (_hwhole : V (Fin.last m) = ⊤)
    (_hincreasing : ∀ r : Fin m, V r.castSucc ≤ V r.succ)
    (_hstable : ∀ r : Fin (m + 1),
      Submodule.map M.frobenius.toLinearMap (V r) = V r),
    ∀ r : Fin m,
      ∃ (wr : ℝ)
        (G : (↥(V r.succ) ⧸
            ((V r.castSucc : Submodule K M.carrier).comap (V r.succ).subtype)) ≃ₗ[K]
          (↥(V r.succ) ⧸
            ((V r.castSucc : Submodule K M.carrier).comap (V r.succ).subtype))),
        wr ≤ w ∧
        (∀ (x : V r.succ) (hx : M.frobenius (x : M.carrier) ∈ V r.succ),
          G (Submodule.Quotient.mk x) =
            Submodule.Quotient.mk ⟨M.frobenius x, hx⟩) ∧
        FrobeniusModule.IsPureOfWeight iota q
          { carrier := ↥(V r.succ) ⧸
              ((V r.castSucc : Submodule K M.carrier).comap (V r.succ).subtype)
            frobenius := G } wr

end FrobeniusModule
