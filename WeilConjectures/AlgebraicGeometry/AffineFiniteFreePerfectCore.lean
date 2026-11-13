/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeModelComplex
import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeModelBounded
import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeModelRetracts

/-! # Strict perfectness of the explicit affine finite free model

## References

* Stacks Project, Tags 068C and 08C4
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The explicitly sheafified and extended bounded finite free complex is strictly perfect
(Stacks, Tags 068C and 08C4). -/
theorem affine_finite_free_perfect_core {Y : Scheme.{u}}
    (U : Y.Opens) (hU : IsAffineOpen U)
    (K : ChainComplex (ModuleCat.{u} (Γ(Y, U) : Type u)) ℕ) (r : ℕ)
    (hfree : ∀ n, Module.Free (Γ(Y, U) : Type u) (K.X n))
    (hfinite : ∀ n, Module.Finite (Γ(Y, U) : Type u) (K.X n))
    (hzero : ∀ n, r < n → IsZero (K.X n)) :
    Scheme.IsStrictlyPerfect Y U (affineFiniteFreeModelComplex U hU K) := by
  refine ⟨affine_finite_free_model_bounded U hU K r hzero, ?_⟩
  exact affine_finite_free_model_retracts U hU K hfree hfinite

end AlgebraicGeometry
