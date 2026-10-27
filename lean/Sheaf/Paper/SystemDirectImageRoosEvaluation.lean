/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.SystemDirectImageRoosExistence

/-! # Finite evaluation of the direct-image Roos object

This is the projection and finite-evaluation part of the direct-image Roos
comparison.  The object and its comparison isomorphism are parameters; the
statement supplies the simultaneously normalized finite evaluation
isomorphisms and their actual projection equations.
(blueprint: stage3-weil-system-direct-image-roos-evaluation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Finite evaluations of a chosen direct-image Roos object are compatible with
the actual total-limit projections.
Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Project, Tag 0941.
Proof: use one K-injective representative of the reduced system.  The
section-normalized derived evaluation comparison gives the isomorphism at each
finite level; normalization of quotient transitions identifies the transported
tower arrows with `sfDirectImageTransition`.  Transporting the canonical
projection of the resulting Roos triangle gives the displayed equation.
No completeness, boundedness, constructibility, or geometric hypotheses are
used. -/
theorem systemDirectImage_roosEvaluation
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(integralComparisonSequenceDirectImage l E f).Additive]
    [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)]
    (S : CoefficientDerivedSystemCalculus l E X)
    (K : DerivedCategory (scalarReductionSource l E X))
    [HasProduct (sfDirectImageTerm l E f K)]
    (L : SfIntegralDirectImage l E f K)
    (e : (coefficientSequenceLimit l E Y).obj
      ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
        (S.reduction.obj K)) ≅ L.obj) :
    ∃ a : ∀ n : ℕ, (coefficientSequenceDerivedEvaluation l E Y n).obj
        ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
          (S.reduction.obj K)) ≅ sfFiniteDerivedDirectImage l E f K n,
      ∀ n : ℕ,
        (coefficientSequenceProjection l E Y n).app
            ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
              (S.reduction.obj K)) ≫
          (coefficientFiniteDerivedRestriction l E Y n).map (a n).hom =
        e.hom ≫ L.projection ≫ Pi.π (sfDirectImageTerm l E f K) n := by
  sorry

end WeilConjectures
