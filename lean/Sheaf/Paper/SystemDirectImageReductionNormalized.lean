/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.IntegralComparisonSequenceSystems

/-! # Normalization of the direct image of a reduction system

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 0941 and 099N.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The whole-system direct image of a reduction system is normalized.
This asserts only the universal finite quotient transition property. It does not
choose a limit, a finite evaluation comparison, or a map of Roos triangles.
Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 0941 and 099N;
Bhatt--Scholze, Lemma 6.5.11(3).
(blueprint: lem-weil-system-direct-image-reduction-normalized).

Proof: put F = sfCompletedDerivedDirectImage(f). Choose one K-injective
resolution of S.reduction(K) on the sequence site. The sectionwise ordinary
direct-image evaluation square, followed by its derived comparison, identifies
the nth evaluation of its direct image with Rf_*(K tensor^L B_n). The specified
K-flat reduction model identifies the source quotient maps with those of K.
The two-term free completed-coefficient resolution of B_n makes the projection
formula F(K) tensor^L B_n -> Rf_*(K tensor^L B_n) an isomorphism, without any
bound on K or on the cohomological dimension of f. These comparisons commute
with the quotient maps B_m -> B_n: on the two-term resolutions, quotient is
given by identity in degree zero and multiplication by the intervening
uniformizer power in degree minus one. Naturality of the derived direct-image
unit, and the section normalization of the restriction comparison, identify
their transported quotient maps with the actual derived transitions of the
sequence-site direct image. Thus its finite objects and transitions are
isomorphic to the finite reduction system of F(K). Associativity of derived
scalar extension shows that each transition-adjoint of that reduction system
is an isomorphism: (F(K) tensor^L B_m) tensor^L_B_m B_n = F(K) tensor^L B_n.
Transport this across the comparison isomorphisms. By the scalar adjunction,
precomposition with each transition is a bijection on the Hom sets in the
definition of IsNormalizedCoefficientSequence. The argument includes n=0,
identity quotient maps, zero complexes and empty schemes. -/
theorem systemDirectImage_reduction_normalized
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(integralComparisonSequenceDirectImage l E f).Additive]
    [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)]
    (S : CoefficientDerivedSystemCalculus l E X)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    IsNormalizedCoefficientSequence l E Y
      ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
        (S.reduction.obj K)) := by sorry

end WeilConjectures
