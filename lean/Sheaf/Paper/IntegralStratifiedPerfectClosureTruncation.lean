module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.Scheme

/-- Standard truncations preserve bounded constructible completeness under the hypotheses
of the integral stratified characterization.
Source: Bhatt--Scholze, Proposition 6.8.11(3). The proof uses the uniform-complete
triangulated interface and the standard t-structure truncation bounds.
(blueprint: lem-weil-pbc-integral-stratified-perfect-closure-truncation). -/
theorem integralStratifiedPerfectClosure_truncation
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hl : IsUnit (l : Γ(T, ⊤))) (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (hK : PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K) (n : ℤ) :
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
      ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
      ((DerivedCategory.TStructure.t.truncGE n).obj K) := by
  sorry

end AlgebraicGeometry.Scheme

