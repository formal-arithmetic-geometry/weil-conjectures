/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.Paper.DerivedPullbackTensorConstraints
import Sheaf.CategoryTheory.BilinearCoefficientDescent
import Sheaf.Paper.PullbackTensorIntegralCompositionCoherence

/-! Rational coefficient component of pullback/tensor composition coherence.

Source: Stacks 07A4 and 0941; this is the rational part of
`lem-pur-pullback-tensor-composition-coherence`.
(blueprint: lem-pur-pullback-tensor-composition-coherence)

Localize the normalized integral quotient-tower composition equation. The
object and morphism normalization specifications identify every localized
comparison and compositor with its prescribed rational construction. Bilinearity
of localization identifies the tensor of the two compositor components.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Rational component of higher pullback/tensor composition coherence.
Source: Stacks 07A4 and 0941; localization of the integral composition square.
(blueprint: lem-pur-pullback-tensor-composition-coherence). -/
theorem pullbackTensorRationalCompositionCoherence {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)] :
    ∀ M N : sfRationalConstructibleCategory l E Y,
      canonicalRationalPullbackTensor_composition l E f h M N := by sorry

end WeilConjectures
