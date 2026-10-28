/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicCompletedTensorCommonLiftTensorUnit
import Sheaf.CategoryTheory.TensorUnitComparisonUnique

/-! Right-unit equation for the common-stage completed tensor lift.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: new-sf-adic-completed-tensor-common-lift-constraints-right-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  (R : LocallyFiniteAdicRealization.Realization l X)
  [∀ x : X, Invertible (l : X.residueField x)]
  (closed : CoefficientClosedStructure (ambientHom l X R))
  (models : CoefficientTensorModels.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R) closed)
  (symmetry : @SymmetricCategory _ _ closed.monoidal)

/-- Arbitrary unit comparisons cannot all satisfy the right-unit law when the
native tensor unit has a nonidentity automorphism.
Source: cancellation in the monoidal functor unit equation, using the unit object
of BS Remark 6.8.15; Mathlib's left-unitor natural isomorphism.
(blueprint: lem-sf-adic-completed-tensor-right-unit-not-universal).

Proof: fix the tensorator and compare data.unit with e followed by data.unit.
If the universal equation held, its instances at the common coefficient unit
would identify the two tensor maps after the same tensorator and mapped right
unitor. Their composite is invertible, so cancel it. Tensoring on the left by
the ordinary image of the coefficient unit is faithful, because data.unit
identifies that image with the native tensor unit. Hence the unit maps agree.
Cancel data.unit to deduce that e is the identity, contrary to the hypothesis.
No nonemptiness or characteristic hypothesis is hidden: the nonidentity
unit automorphism is supplied explicitly; the empty scheme need not admit one. -/
theorem completed_tensor_common_lift_right_unit_not_universal
    (data : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry)
    (e : closed.monoidal.tensorUnit ≅ closed.monoidal.tensorUnit)
    (he : e.hom ≠ 𝟙 _) :
    ¬ (∀ d : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry,
      ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
        closed.tensor.map (Prod.mkHom (𝟙 _) d.unit.hom) ≫
            d.tensor.hom.app (A, pullbackTensorCommonUnit l (PadicAlgCl l) X) ≫
            (ordinary l X R).map
              (pullbackTensorCommonRightUnitor l (PadicAlgCl l) X A).hom =
          (closed.monoidal.rightUnitor ((ordinary l X R).obj A)).hom) := by
  let := closed.monoidal
  intro h
  let U := pullbackTensorCommonUnit l (PadicAlgCl l) X
  let d : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry :=
    { tensor := data.tensor
      unit := e ≪≫ data.unit }
  let q := data.tensor.app (U, U) ≪≫
    (ordinary l X R).mapIso (pullbackTensorCommonRightUnitor l (PadicAlgCl l) X U)
  have hu : data.unit.hom = d.unit.hom :=
    tensorUnitComparison_unique data.unit q data.unit.hom d.unit.hom
      ((h data U).trans (h d U).symm)
  apply he
  apply (cancel_mono data.unit.hom).1
  simpa only [d, Iso.trans_hom, Category.id_comp] using hu.symm

-- STATEMENT-DISPUTED: data.unit is arbitrary, so the equation is asserted for every
-- isomorphism from the native unit. The theorem just above refutes that universal
-- assertion whenever the native unit has a nonidentity automorphism. In a nonzero
-- characteristic-zero coefficient category, negation supplies such an automorphism.
-- The finite models N and native coherence do not constrain data.unit or data.tensor.
/-- The right-unit component of the common-stage constraint system.
The finite coefficient multiplication calculation and its transport through the
native right unitor are the proof obligations isolated here.
(blueprint: new-sf-adic-completed-tensor-common-lift-constraints-right-unit). -/
theorem completed_tensor_common_lift_constraints_right_unit
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry)
    (data : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry) :
    ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
      closed.tensor.map (Prod.mkHom (𝟙 _) data.unit.hom) ≫
          data.tensor.hom.app (A, pullbackTensorCommonUnit l (PadicAlgCl l) X) ≫
          (ordinary l X R).map (pullbackTensorCommonRightUnitor l (PadicAlgCl l) X A).hom =
        (closed.monoidal.rightUnitor ((ordinary l X R).obj A)).hom := by
  sorry

end WeilConjectures.AdicQbarRealization
