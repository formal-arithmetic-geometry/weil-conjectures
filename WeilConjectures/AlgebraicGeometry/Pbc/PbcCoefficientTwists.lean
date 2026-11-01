/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FixedFinitePositiveCoefficientTwist
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCohomologySheaves

/-! # The recorded Tate twists in the PBC finite-stage coordinates

Source: blueprint def-coefficient-twists-detailed, signed powers and tensor with a complex;
Bhatt--Scholze, Section 6.8 (blueprint: def-coefficient-twists-detailed).
All roots, signed powers and coefficient identifications are the published ones.
The only new construction is their transport to the PBC completed coefficient ring.
The original finite, integral, rational and intrinsic Qbar interfaces remain imported.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
open WeilConjectures
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  [IsNoetherian X]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- The recorded signed root line, transported along the fixed coefficient isomorphism.
Source: blueprint signed-power definition
(blueprint: def-coefficient-twists-detailed). -/
def pbcTateLineSheaf (m : ℤ) : pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) :=
  (pbcRestrict (purCoefficientIso l E X).hom).obj
    (coefficientTwistLine X
      (R := completedIntegralCommRingSheafUnrestricted l E X) (purTwistIntegralModule X l E) m)

/-- Ordinary sheaf tensor by the same line, in the actual PBC module category.
Source: blueprint tensor-twist definition
(blueprint: def-coefficient-twists-detailed). -/
def pbcTateSheafTensor (m : ℤ) :
    pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) ⥤
      pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) :=
  purOrdinaryCoefficientModel l E X ⋙ integralSheafTwist l E X m ⋙
    pbcRestrict (purCoefficientIso l E X).hom

/-- The actual derived tensor: flatness permits termwise tensor on every complex.
Source: blueprint tensor-twist definition
(blueprint: def-coefficient-twists-detailed). -/
def pbcTateAmbient (m : ℤ) :
    PbcCompletedDerived X (pbcIntegralDatum l E) ⥤
      PbcCompletedDerived X (pbcIntegralDatum l E) :=
  (pbcTateSheafTensor l X E m).mapDerivedCategory

/-- Tensor by the root line preserves the three defining integral conditions.
Source: blueprint integral tensor-twist definition
(blueprint: def-coefficient-twists-detailed).
Proof: locally trivialize the root line on its compatible primitive-root covers.
Its positive powers, the unit, and its dual powers are invertible lines. Tensor
is locally the identity, commutes with each finite reduction, and preserves the
common bounded interval, stratification and normalized etale-origin witnesses.
It also preserves the completion comparison: a finite projective factor commutes
with the reduction tower and its derived limit. Descend along these covers and
transport through the finite-projection-normalized coefficient isomorphism. -/
theorem pbcTateAmbient_mem [IsNoetherian X]
    (_hDim : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (m : ℤ) (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)) :
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((pbcTateAmbient l X E m).obj K.obj) := by
  sorry

/-- Rational tensor by the actual signed line at the specified finite field.
Source: blueprint rational tensor-twist definition
(blueprint: def-coefficient-twists-detailed). -/
def pbcTateRational (F : Padic.FiniteCoefficientFields l Ω) (m : ℤ) :
    pbcStageCategory l Ω X F ⥤ pbcStageCategory l Ω X F :=
  pbcConditionalRational (pbcStageDatum.{u} l Ω F)
    (pbcTateAmbient l X (pbcFiniteField.{u} l Ω F) m)
    (pbcTateAmbient_mem l X (pbcFiniteField.{u} l Ω F) hDim.out m)
    (pbcStageUniformizer.{u} l Ω F)

end AlgebraicGeometry.Scheme
