/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q9
-/
module

public import Sheaf.SixFunctors.IntegralDualizingMappingTower
public import Sheaf.SixFunctors.CoefTowerEvaluationPairingData

/-! # Quotient-system Hom at the geometric coefficient point

Source: prop-coef-integral-dualizing, proof paragraph 2, final scalar adjunction.
(blueprint: lem-coef-point-integral-reduction-hom-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

include hl in
/-- Scalar adjunction for reductions of integral constructible complexes on the point.
There is no compactification or compact-support operation in this assertion.

Source: prop-coef-integral-dualizing, second proof paragraph, last comparison;
point_sections_derived_reduction and the point reconstruction counit.
(blueprint: lem-coef-point-integral-reduction-hom-tower).

Proof: use the constant-module extension/point-sections adjunction at the completed
coefficient sheaf. Its derived counit is invertible on integral constructible
complexes by pointSectionsReconstruction. Thus such a complex N is reconstructed
from its integral R-module section complex C. Resolve C by a flat-term K-flat
complex P. Constant extension of P followed by the actual sequence completion
projection computes S.reduction(N), by the reductionModel of S. The point
reduction unit comparison identifies its sections with P tensor the actual
quotient ring system, simultaneously, with every quotient transition.
For a quotient-system target Q, scalar internal-Hom adjunction on the sequence
site gives restricted RHom_Q(S.reduction(N),Q) as RHom from the constant integral
input into Res Q. The point extension/sections adjunction then gives the strict
R-module Hom tower Hom_R(P,I_n), where I is one simultaneous K-injective
resolution of the restricted section tower. Specialize Q to T's tensor unit.
The tensor model identifies that unit with the regular quotient sheaf in degree
zero: both represent identity under the recorded tensor-Hom adjunction.
Its restricted sections are the actual tower A_n in degree zero, including its
quotient maps. Uniqueness of localization comparisons identifies this Hom tower
with integralDualizingCoefficientHomTower. All chain comparisons are natural in
P and invert quasi-isomorphisms, so they descend to the displayed natural
isomorphism. Neither an inverse limit nor finite-level lifting is used. For zero
input every Hom complex is zero, and n=0 means the first positive quotient. -/
theorem point_integral_reduction_hom_tower
    (S : CoefficientDerivedSystemCalculus l E (Spec (.of D.k)))
    (T : CoefficientDerivedSystemTensors l E (Spec (.of D.k))) :
    Nonempty ((sfIntegralConstructible l E (Spec (.of D.k))).ι.op ⋙ S.reduction.op ⋙
      (Functor.curry.obj (coefficientSequenceInternalHom l E (Spec (.of D.k)))).flip.obj
        T.systemClosed.monoidal.tensorUnit ⋙ coefPairingSections l E (Spec (.of D.k)) ≅
      ((sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
        integralDualizingDerivedSections l E (Spec (.of D.k))).op ⋙
          integralDualizingCoefficientHomTower l E) := by sorry

end WeilConjectures
