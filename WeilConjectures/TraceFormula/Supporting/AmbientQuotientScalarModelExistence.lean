/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.TraceFormula.Supporting.AmbientQuotientScalarNormalizationExistence

/-! # Ambient coherent scalar quotient realization

We show that completed scalar change has a natural realization using the entire reduction system,
normalized on every whole-system adjunction-coherent quotient presentation
(`WeilConjectures.ambientQuotientScalarModel_exists`).

## Implementation details

The realization comes from the ordinary quotient extension/restriction adjunction and its derived
comparison with the supplied reduction calculus. On a flat-term K-flat complex, its strict
quotient system is extended through the map of quotient coefficient sheaves; at level `n` the
balanced association sends `(x ⊗ a) ⊗ b` to `x ⊗ ι(a) b`, with inverse `x ⊗ b ↦ (x ⊗ 1) ⊗ b`.
These chain isomorphisms commute with all quotient transitions and restrictions, and the
normalized Roos comparison identifies the resulting total limit with the completed scalar tower.
The derived change-of-rings counit is invertible on K-flat systems, so the comparison descends
along the localization to the ambient derived category. For a coherent presentation
`(C, e, κ)`, `e` is the canonical derived comparison followed by the strict quotient isomorphism
fixed by `κ`, which gives the normalization equation. No invertibility condition on the
characteristic of the scheme is needed.

## References

* [Stacks: Tags 06YY, 0941]
-/

@[expose] public section
set_option autoImplicit false
universe t u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Completed scalar change has a natural realization using the entire reduction
system, normalized on every whole-system adjunction-coherent quotient presentation. -/
theorem ambientQuotientScalarModel_exists (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l L X) :
    Nonempty (IntegralComparisonScalarModel l E L ι X S ρ) := by
  obtain ⟨realization, hnormalization⟩ :=
    ambientQuotientScalarModel_normalization_exists l E L ι X S ρ
  exact ⟨⟨realization, hnormalization⟩⟩

end WeilConjectures
