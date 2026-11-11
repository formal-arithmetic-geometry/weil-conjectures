/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TraceIsomorphism

/-!
# The trace isomorphism in top degree for proper varieties, with `ℚ̄_ℓ` coefficients

Let `X₀` be smooth, proper and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`.
Then `H^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ(-d)`: there is an isomorphism `H^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ` on
which the geometric Frobenius acts by `q^d`
(`AlgebraicGeometry.WeilSheaf.exists_linearEquiv_cohomology_two_mul_adicConstant`). This is the
proper clause of `AlgebraicGeometry.WeilSheaf.traceIsomorphism_adicConstant`; see
`WeilConjectures.WeilSheaf.TraceIsomorphism` for the existential form.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  (d : ℕ) [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `theorem-trace-isomorphism-top-degree--9` (the trace isomorphism with coefficients
`ℚ̄_ℓ`): for `X₀` smooth, proper and geometrically connected of pure dimension `d` over
`k₀ = 𝔽_q`, there is an isomorphism `tr : H^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ(-d)`, that is an isomorphism
`H^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ` on which the geometric Frobenius acts by `q^d`. The trace map
itself is not available for Weil sheaves, hence the existential form
(`AlgebraicGeometry.WeilSheaf.traceIsomorphism_adicConstant`). -/
theorem exists_linearEquiv_cohomology_two_mul_adicConstant :
    ∃ tr : ((adicConstant k₀ l X).cohomology (2 * d)).carrier ≃ₗ[PadicAlgCl l] PadicAlgCl l,
      ∀ z, tr (((adicConstant k₀ l X).cohomology (2 * d)).frobenius z) =
        (Nat.card k₀ : PadicAlgCl l) ^ d * tr z :=
  (traceIsomorphism_adicConstant k₀ l X d).2.2.2 inferInstance

end WeilSheaf

end AlgebraicGeometry
