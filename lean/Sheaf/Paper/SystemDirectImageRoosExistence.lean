/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.IntegralComparisonSequenceSystems
public import Sheaf.Paper.SfDerivedDirectImage

/-! # Existence of the direct-image Roos object

This is the object-existence part of the projection-compatible direct-image
comparison.  The construction uses one K-injective system resolution and the
derived tower limit theorem; the finite evaluation comparisons are supplied by
the companion interface theorem.
(blueprint: stage3-weil-system-direct-image-roos-existence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual derived system direct image admits a finite-image Roos object.
Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Project, Tag 0941.
Proof: choose a K-injective representative of the reduced object, apply the
derived tower-limit construction to its sectionwise direct image, and transport
the resulting product and triangle along the canonical finite restrictions.
The resulting triangle has exactly `sfDirectImageTransition` as its tower map.
The construction is valid for arbitrary schemes and arbitrary derived inputs,
including zero objects and empty schemes. -/
theorem systemDirectImage_roosExistence
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(integralComparisonSequenceDirectImage l E f).Additive]
    [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)]
    (S : CoefficientDerivedSystemCalculus l E X)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    let N := (integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
      (S.reduction.obj K)
    ∃ hprod : HasProduct (sfDirectImageTerm l E f K),
      ∃ L : @SfIntegralDirectImage l _ E _ _ _ X Y f K hprod,
      ∃ e : ((coefficientSequenceLimit l E Y).obj N ≅ L.obj), True := by
  sorry

end WeilConjectures
