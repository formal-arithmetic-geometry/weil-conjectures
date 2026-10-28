/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.SixFunctors.IntegralDualizingMappingTower
import Sheaf.SixFunctors.IntegralDualizingCoefficientHomTowerComparison

/-! # The coefficient Hom tower over a complete DVR

Source: current blueprint prop-coef-integral-dualizing, final displayed comparison;
Stacks 0941 and 08J9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The limit of Hom from a constant coefficient complex into the quotient tower
is its derived dual. This is purely a coefficient statement and has no scheme,
compact support, or dualizing object among its hypotheses.

Source: current blueprint prop-coef-integral-dualizing, last displayed comparison
in its second proof paragraph; Stacks 0941 and 08J9.
(blueprint: lem-coef-integral-dualizing-coefficient-hom-tower-limit).

Proof: the quotient tower A_n has surjective transitions. On their product solve
x_n-q_n(x_(n+1))=b_n recursively, starting with x_0=0 and choosing a preimage of
x_n-b_n at each successor. Thus 1-shift is surjective and its kernel is the
ordinary inverse limit. Completeness of the coefficient DVR identifies this
kernel, with its actual quotient projections, with R. Consequently the quotient
tower concentrated in degree zero has total derived inverse limit R[0].
For a coefficient complex C, choose a K-flat resolution P and one simultaneous
K-injective resolution I of A_bullet. The closed Hom of constant P into I has
nth value Hom_R(P,I_n). Its transitions are split surjective degreewise, and
Hom_R(P,lim I) = lim Hom_R(P,I_n), including all product terms and signed
differentials. These identifications compute RHom_R(C,R), without a boundedness
or finite generation assumption on C. They commute with precomposition and
homotopies, hence descend to a natural isomorphism of functors. The comparison
between the two tower localization models identifies the same complexes and
fractions, so it preserves this calculation. The tensor unit of D(R) is the
regular module R[0], which is the target in coefficientDerivedDual. -/
theorem integralDualizing_coefficient_hom_tower_limit :
    Nonempty (integralDualizingCoefficientHomTower l E ⋙
      CoefTower.totalLimit (integralDualizingCoefficients l E) ≅
        coefficientDerivedDual (integralDualizingCoefficients l E)) := by
  obtain ⟨α, hα⟩ := integralDualizing_coefficient_hom_tower_comparison l E
  let e : integralDualizingCoefficientHomTower l E ⋙
      CoefTower.totalLimit (integralDualizingCoefficients l E) ≅
      coefficientDerivedDual (integralDualizingCoefficients l E) :=
    NatIso.ofComponents (fun C ↦ asIso (α.app C)) (by
      intro C D f
      exact α.naturality f)
  exact ⟨e⟩

end WeilConjectures
