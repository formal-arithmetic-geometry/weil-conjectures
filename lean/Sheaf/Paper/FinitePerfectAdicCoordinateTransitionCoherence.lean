/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W5
-/
module

public import Sheaf.Paper.FinitePerfectAdicMarkedOrigin
public import Sheaf.Paper.FinitePerfectAdicScalarCoherence

/-! # Coherence of finite perfect adic coordinate transitions

Source: Stacks Project, Tags 09AL, 09C6 and 06YY.

This is the compatibility equation part of
`finitePerfectAdic_descend_coordinate_transitions`.
(blueprint: new-w5-finite-perfect-adic-coordinate-transition-coherence)
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
The scalar-realization comparisons intertwine every consecutive transition
with the strict completed quotient tower.

Source: Stacks Project, Tags 06YY and 09C6.
(blueprint: new-w5-finite-perfect-adic-coordinate-transition-coherence)
-/
theorem finitePerfectAdic_coordinate_transition_coherence
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
      finitePerfectAdicQuotientCoordinates X d φ M V n)
    (dK : ∀ n : ℕ, K (n + 1) ⟶
      (normalizationRestrict V.left.smallEtaleTopology
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj (K n))
    (actual : ∀ (U : V.left.ProEt) (W : X.ProEt)
        (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
        (finitePerfectAdicScalarRealization X d V U W f n).obj
          ((localProEtaleComparison U.hom
            (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj (K n)) ≅
        (finitePerfectAdicRestrictedTower X d W
          ((completedAdicReduction X d).obj M)).obj (op n)) :
    ∀ (U : V.left.ProEt) (W : X.ProEt)
      (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
      (finitePerfectAdicScalarRealization X d V U W f (n + 1)).map
          (localProEtaleNormalization U.hom
            (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
            (dK n)) ≫
        (finitePerfectAdicScalarCoherence X d V U W f n).hom.app
          ((localProEtaleComparison U.hom
            (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj (K n)) ≫
        (actual U W f n).hom =
      (actual U W f (n + 1)).hom ≫
        (finitePerfectAdicRestrictedTower X d W
          ((completedAdicReduction X d).obj M)).map
            (homOfLE (Nat.le_succ n)).op := by sorry

end AlgebraicGeometry.Scheme
