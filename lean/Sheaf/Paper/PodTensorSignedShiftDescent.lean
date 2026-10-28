/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.PodTensorSignedShiftTowers

/-! # Descent of strict signed tensor shifts to the completed tensor

The strict tower maps and their generator rules are already fixed. The remaining
step extends their Roos-normalized localizations to the completed derived tensor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.sfIntegralConstructible
  WeilConjectures.podReindexCalculus

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Descend the two already fixed strict tensor shift maps to the completed derived
tensor, retaining the normalization on every good representative.

Source: Stacks 07A4 (descent on K-flat representatives), 011G (signed shifts),
and 0941 (the Roos model); blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: lem-pod-tensor-signed-shift-descent).

Proof: good complexes are stable under shifts by podTensorGoodShift. For each
integer r, form the natural isomorphisms on pairs of good complexes by composing
the representative comparison, the explicit strict tower shift, the given signed
Roos shift, the localization shift, and the inverse shifted representative
comparison. Naturality of the tower maps follows from their finite summand
formulas. Naturality of the signed Roos map follows by composing with the two
cone projections: its two defining laws give the same maps on both coordinates,
and these coordinates jointly determine a map of the underlying graded objects.
The product of good-representative localizations is a localization. Its fully
faithful precomposition therefore uniquely extends these natural isomorphisms
to the completed derived tensor. For arbitrary identifications a and b of shifted
inputs, precompose the extended maps with the tensor of a or b and the identity.
Naturality with respect to eP, eQ, eP', eQ' and the two given equations identifying
a and b with the localization shifts gives exactly both equations of Model.
The construction works for all integer shifts and requires no boundedness of the
good representatives. It uses the specified Roos comparison, not an independently
chosen shift. -/
theorem podTensorSignedShiftDescent (W : Scheme.{u})
    (ρ : PodSignedRoosShift (scalarReductionSource l E W)) (hρ : ρ.Laws) :
    ∃ L : PodTensorDerivedShiftLeft l E W, ∃ R : PodTensorDerivedShiftRight l E W,
      (podTensorSignedShiftOfDerived l E W L R).Model l E ρ := by
  sorry

end WeilConjectures
