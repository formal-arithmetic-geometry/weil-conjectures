/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W5
-/
module

public import Sheaf.Paper.FinitePerfectAdicMarkedOrigin
public import Sheaf.Paper.FinitePerfectAdicScalarCoherence

/-! # Transition maps between specified finite perfect adic origins

Source: Stacks Project, Tags 09AL, 09C6 and 06YY.

This is the transition-map and universality part of
`finitePerfectAdic_descend_coordinate_transitions`.
(blueprint: new-w5-finite-perfect-adic-coordinate-transition-maps)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/--
The supplied comparisons of finite quotient coordinates determine consecutive
coefficient-restricted arrows.  Each arrow is universal after etale pullback.

Source: Stacks Project, Tags 09AL and 09C6; balancing in Tag 06YY.
(blueprint: new-w5-finite-perfect-adic-coordinate-transition-maps)
-/
theorem finitePerfectAdic_coordinate_transition_maps
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n))
    (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (K : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))))
    (hKplus : ∀ n : ℕ, DerivedCategory.TStructure.t.plus (K n))
    (e : ∀ n : ℕ, ((ProEtale.comparisonUpperStar
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) V.left)
        |>.mapDerivedCategory).obj (K n) ≅
      finitePerfectAdicQuotientCoordinates X d φ M V n) :
    ∃ dK : ∀ n : ℕ, K (n + 1) ⟶
        (normalizationRestrict V.left.smallEtaleTopology
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj (K n),
      ∀ (n : ℕ) (U : V.left.Etale), Nonempty (StructuredArrow.IsUniversal
        (StructuredArrow.mk (etaleIsomorphismNormalizationArrow V.left
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
          (dK n) U))) := by sorry

end AlgebraicGeometry.Scheme
