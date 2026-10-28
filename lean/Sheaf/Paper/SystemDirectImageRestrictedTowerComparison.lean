/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.IntegralComparisonSequenceSystems
public import Sheaf.Paper.SfDerivedDirectImage

/-! # The restricted tower of the actual system direct image

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Tag 0D6E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

/-- A representing complex of the restricted system direct image evaluates to the
finite-image tower, including its actual adjacent arrows. This comparison contains
no inverse-limit object, product, projection or distinguished-triangle assertion.
Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Tags 0D6E and 06YY.
(blueprint: stage3-weil-system-direct-image-restricted-tower-comparison).

Proof: choose a flat-term K-flat complex P representing K. The reductionModel field
of S supplies a strict quotient complex C and its simultaneous finite comparisons;
its transition equation identifies the quotient arrows with ordinary scalar reduction.
Resolve C once by a K-injective system J and apply the sequence direct image to J.
The ordinary evaluation/direct-image square is identity on sections. Derived
ringed-topos composition identifies its finite evaluations with the corresponding
finite derived direct images; its resolution normalization retains the same arrows.
Restrict to completed coefficients. On P, the quotient arrow is the map sending
s tensor x to rho(s) tensor x, hence is sfDerivedReductionTransition by its unique
representative characterization. The restriction/direct-image square is the
section-normalized sfDerivedRestrictionComparison, so transporting this arrow gives
exactly sfDirectImageTransition. These identifications yield an isomorphism of the
whole evaluated tower of this representative with Functor.ofOpSequence of those
arrows. Exact evaluation sends quasi-isomorphisms of strict towers to objectwise
isomorphisms after localization. Localization's factorization of simultaneous
evaluation therefore transports the comparison along e to any representing T.
This uses no boundedness, constructibility, completeness, or geometric hypothesis;
it applies also to zero complexes and empty schemes. -/
theorem systemDirectImage_restrictedTowerComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(integralComparisonSequenceDirectImage l E f).Additive]
    [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)]
    (S : CoefficientDerivedSystemCalculus l E X)
    (K : DerivedCategory (scalarReductionSource l E X))
    (T : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ℤ)
    (e : DerivedCategory.Q.obj T ≅ (coefficientSequenceDerivedRestriction l E Y).obj
      ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
        (S.reduction.obj K))) :
    Nonempty (T.asFunctor ⋙ DerivedCategory.Q ≅
      Functor.ofOpSequence (sfDirectImageTransition l E f K)) := by sorry

end WeilConjectures
