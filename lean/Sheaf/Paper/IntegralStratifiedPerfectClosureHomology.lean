module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.Scheme

/-- Cohomology sheaves in degree zero preserve bounded constructible completeness under
the hypotheses of the integral stratified characterization.
Source: Bhatt--Scholze, Proposition 6.8.11(3). The proof uses the bounded Postnikov
devissage and the degree-zero local-module resolution.
(blueprint: lem-weil-pbc-integral-stratified-perfect-closure-homology). -/
theorem integralStratifiedPerfectClosure_homology
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hl : IsUnit (l : Γ(T, ⊤))) (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (hK : PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K) (q : ℤ) :
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
      ((DerivedCategory.singleFunctor _ 0).obj
        ((DerivedCategory.homologyFunctor _ q).obj K)) := by
  sorry

end AlgebraicGeometry.Scheme

