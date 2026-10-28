/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W5
-/
module

public import Sheaf.Paper.FinitePerfectAdicMarkedOrigin
public import Sheaf.Paper.FinitePerfectAdicScalarCoherence

/-! # Scalar realizations of finite perfect adic origins

Source: Stacks Project, Tags 09AL, 09C6 and 06YY.

This is the realization part of
`finitePerfectAdic_descend_coordinate_transitions`.
(blueprint: new-w5-finite-perfect-adic-coordinate-realizations)
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
Each supplied finite quotient comparison admits the actual scalar-realization
isomorphisms on every chart and pro-etale restriction.

Source: Stacks Project, Tags 09C6 and 06YY.
(blueprint: new-w5-finite-perfect-adic-coordinate-realizations)
-/
theorem finitePerfectAdic_coordinate_realizations
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
    ∃ actual : ∀ (U : V.left.ProEt) (W : X.ProEt)
        (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
        (finitePerfectAdicScalarRealization X d V U W f n).obj
          ((localProEtaleComparison U.hom
            (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj (K n)) ≅
        (finitePerfectAdicRestrictedTower X d W
          ((completedAdicReduction X d).obj M)).obj (op n), True := by sorry

end AlgebraicGeometry.Scheme
