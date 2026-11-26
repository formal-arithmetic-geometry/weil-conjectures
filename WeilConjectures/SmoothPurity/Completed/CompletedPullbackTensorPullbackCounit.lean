/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.TraceFormula.Supporting.TransportedReductionSystemsNormalized
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus

/-! # Pullback components of the completed pullback counit comparison

The reconstruction counit is invertible on the derived inverse image of a reduced system.

## References

* Stacks Project, Tag 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
namespace WeilConjectures

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The reconstruction counit on the derived inverse image, along the sequence pullback `G`,
of the reduction of `M` is an isomorphism. -/
theorem completedPullbackTensor_pullback_counit
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (C : CoefficientDerivedSystemCalculus l E X)
    (D : CoefficientDerivedSystemCalculus l E Y)
    (G : coefficientSequenceModules l E Y ⥤ coefficientSequenceModules l E X)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (hG : G = integralComparisonSequencePullback l E f)
    (M : DerivedCategory (scalarReductionSource l E Y)) :
    IsIso (C.adjunction.counit.app
      ((G.mapDerivedCategory).obj
        (D.reduction.obj M))) := by
  subst G
  have hN : IsNormalizedCoefficientSequence l E X
      ((integralComparisonDerivedSequencePullback l E f).obj (D.reduction.obj M)) :=
    (transportedReductionSystems_normalized l E E (AlgHom.id _ _)
      f _hX _hY D).1 M
  exact ((purNormalizedReconstructionOfScheme l E X C).1 _ hN).2

end WeilConjectures
