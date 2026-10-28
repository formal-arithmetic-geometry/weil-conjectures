/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M9
-/
module

public import Sheaf.SixFunctors.RationalVerdierTensorTowerSignedCoordinate

/-! # Coherent signed braiding in the strict Roos tensor model

Source: Stacks 06YL, 08TC and 0941.
(blueprint: lem-coef-rational-verdier-tensor-roos-signed-model). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalVerdier
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The coherent derived braiding is represented by the strict tower signed map.
There is no ordinary tensor augmentation in this statement: both source and target
are already completed tensor models.

Source: Stacks 06YL, 08TC, 0941; full tensor-model normalization and the signed
representative clause of the coherent braiding.
(blueprint: lem-coef-rational-verdier-tensor-roos-signed-model).

Proof: expand the reference tensor model into reduction, the coherent K-flat
comparison, the Roos limit model and the strict tensor-tower comparison. Coherent
reduction preserves K-flatness of the good inputs. The representative equation
for pullbackTensorBraiding identifies the signed total map with its derived
braiding after the coherent K-flat comparisons. Naturality of the limit/Roos
isomorphism transports it to Roos of the restricted signed map. The remaining
strict tensor-tower comparisons give precisely strictTensorSignedSwap. Cancel
the model isomorphisms on the two sides. No completeness of the inputs is used. -/
theorem tensor_roos_signed_model
    (P Q : (integralOperationsGoodComplex l E X).FullSubcategory) :
    DerivedCategory.Q.map
        (integralOperationsRoosFunctor.map (strictTensorSignedSwap l E X P.obj Q.obj)) ≫
        (pullbackTensorReferenceTensorModel l E X Q P).inv =
      (pullbackTensorReferenceTensorModel l E X P Q).inv ≫
        (coefficientSequenceLimit l E X).map
          ((pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology X))
            (coefficientSequenceCommRingSheaf l E X)
            (pullbackTensorCalculus l E X).systemClosed
            (pullbackTensorCalculus l E X).systemTensorModel).hom.app
              ((pullbackTensorCalculus l E X).reduction.obj (DerivedCategory.Q.obj P.obj),
               (pullbackTensorCalculus l E X).reduction.obj (DerivedCategory.Q.obj Q.obj))) := by
  sorry

end WeilConjectures.RationalVerdier
