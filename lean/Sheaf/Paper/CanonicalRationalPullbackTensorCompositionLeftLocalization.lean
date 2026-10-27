/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedPullbackTensorConstraints

/-! Localization of the left hand side of rational pullback/tensor composition.
Source: Stacks 07A4 and 0941; normalized localization of the composition square.
(blueprint: lem-pur-pullback-tensor-rational-composition-coherence-left-localization)
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

/-- The left side of rational composition is the localized integral left side.
Source: Stacks 07A4 and 0941; localization of the normalized composition square.
(blueprint: lem-pur-pullback-tensor-rational-composition-coherence-left-localization).
Use the normalization of the rational canonical tensor and compositor, together with
bilinearity of localized tensor, to identify the left composite with the localization
of the integral left composite. Endpoint normalization supplies the displayed HEq.
-/
theorem canonicalRationalPullbackTensorComposition_left_localization {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfRationalConstructibleCategory l E Y) :
    HEq
      ((canonicalRationalPullbackTensor l E (h ≫ f) M N).hom ≫
        (rationalDerivedTensor l E Z).map (Prod.mkHom
          (pullbackTensorRationalComposition l E f h M).hom
          (pullbackTensorRationalComposition l E f h N).hom))
      ((sfRationalConstructibleLocalization l E Z).map
        ((canonicalIntegralPullbackTensor l E (h ≫ f) M.obj N.obj).hom ≫
          (constructibleIntegralTensor l E Z).map (Prod.mkHom
            ((pullbackTensorIntegralComposition l E f h).hom.app M.obj)
            ((pullbackTensorIntegralComposition l E f h).hom.app N.obj)))) := by
  sorry

end WeilConjectures
