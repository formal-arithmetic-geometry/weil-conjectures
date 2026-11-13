/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicMarkedOrigin
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientCoordinateTower
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicCoordinateTransitionCoherence

/-! # Descending the arrows of already descended finite quotients

Source: Stacks Project, Tags 09AL, 09C6 and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Once the finite quotients have specified bounded-below etale origins, their
consecutive maps descend and their scalar realizations compare with the actual tower.
This asserts neither existence of those origins nor any local marking, finite local
constancy, perfectness or geometric-stalk property. The comparisons supplied in the
hypothesis identify the actual quotients, rather than just their isomorphism classes
at geometric points. The assertion applies to every supplied family of origins and
comparison isomorphisms.

Source: Stacks Project, Tag 09C6, the arrows L_(n+1) -> L_n, using full faithfulness
in Tag 09AL and derived tensor balancing in Tag 06YY. -/
theorem finitePerfectAdic_descend_coordinate_transitions
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (K : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))))
    (hKplus : ∀ n : ℕ, DerivedCategory.TStructure.t.plus (K n))
    (e : ∀ n : ℕ, ((ProEtale.comparisonUpperStar
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) V.left)
        |>.mapDerivedCategory).obj (K n) ≅ finitePerfectAdicQuotientCoordinates X d φ M V n) :
    ∃ dK : ∀ n : ℕ, K (n + 1) ⟶
        (normalizationRestrict V.left.smallEtaleTopology
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj (K n),
    ∃ actual : ∀ (U : V.left.ProEt) (W : X.ProEt)
        (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
        (finitePerfectAdicScalarRealization X d V U W f n).obj
          ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
            (K n)) ≅
        (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).obj
          (op n),
      (∀ (n : ℕ) (U : V.left.Etale), Nonempty (StructuredArrow.IsUniversal
        (StructuredArrow.mk (etaleIsomorphismNormalizationArrow V.left
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) (dK n) U)))) ∧
      (∀ (U : V.left.ProEt) (W : X.ProEt)
        (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
        (finitePerfectAdicScalarRealization X d V U W f (n + 1)).map
          (localProEtaleNormalization U.hom
            (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) (dK n)) ≫
          (finitePerfectAdicScalarCoherence X d V U W f n).hom.app
            ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
              (K n)) ≫
          (actual U W f n).hom =
        (actual U W f (n + 1)).hom ≫
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).map
            (homOfLE (Nat.le_succ n)).op) := by
  obtain ⟨dJ, hJ, actualJ, hactualJ⟩ := finitePerfectAdic_quotient_coordinate_tower
    X d φ hφ hcompat M V
  exact finitePerfectAdic_coordinate_transition_coherence
    X d φ M V K hKplus e dJ hJ actualJ hactualJ

end AlgebraicGeometry.Scheme
