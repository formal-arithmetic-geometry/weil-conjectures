module

public import Sheaf.AlgebraicGeometry.AffineFiniteFreeModelComplex

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The explicit affine finite-free model is supported in degrees `[-r, 0]`.
Source: Stacks Project, Tag 068C, extension-by-zero support calculation
(blueprint: lem-affine-finite-free-model-bounded).

The extension along `n ↦ -n` is zero in positive degrees and below `-r`; the
inverse localized-site equivalence preserves zero objects. This is a direct
termwise calculation from the definition of `affineFiniteFreeModelComplex`. -/
theorem affine_finite_free_model_bounded {Y : Scheme.{u}}
    (U : Y.Opens) (hU : IsAffineOpen U)
    (K : ChainComplex (ModuleCat.{u} (Γ(Y, U) : Type u)) ℕ) (r : ℕ)
    (hzero : ∀ n, r < n → IsZero (K.X n)) :
    ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((affineFiniteFreeModelComplex U hU K).X n) := by
  sorry

end AlgebraicGeometry
