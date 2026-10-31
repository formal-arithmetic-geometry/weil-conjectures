/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FinitePerfectAdicConstantNormalization
public import WeilConjectures.AlgebraicGeometry.FinitePerfectAdicStalkModels
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin

/-! # Consecutive normalized arrows for actual finite levels

Source: Stacks Project, Tags 09C6 and 06YY.
(blueprint: lem-weil-pbc-finite-perfect-adic-actual-level-transitions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Full faithfulness of finite-coefficient descent supplies the consecutive maps.
Derived tensor balancing identifies their transposes with the quotient restriction,
which makes each arrow universal.  This statement isolates the transition part of
the levelwise package.  Source: Tags 09C6 and 06YY.
(blueprint: lem-weil-pbc-finite-perfect-adic-actual-level-transitions). -/
theorem finitePerfectAdic_actual_level_transitions
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d)
    (hmark : FinitePerfectAdicLevelMarkings X d φ M V T)
    (K : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))))) :
    ∃ dK : ∀ n : ℕ, K (n + 1) ⟶
      (normalizationRestrict V.left.smallEtaleTopology
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj (K n),
      ∀ n : ℕ, EtaleUniversalNormalization V.left
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) (dK n) := by
  sorry

end AlgebraicGeometry.Scheme
