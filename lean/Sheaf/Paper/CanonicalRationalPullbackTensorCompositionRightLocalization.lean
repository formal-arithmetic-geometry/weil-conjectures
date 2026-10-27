/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedPullbackTensorConstraints

/-! Localization of the right hand side of rational pullback/tensor composition.
Source: Stacks 07A4 and 0941; normalized localization of the composition square.
(blueprint: lem-pur-pullback-tensor-rational-composition-coherence-right-localization)
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

/-- The right side of rational composition is the localized integral right side.
Source: Stacks 07A4 and 0941; localization of the normalized composition square.
(blueprint: lem-pur-pullback-tensor-rational-composition-coherence-right-localization).
Apply the localization formula for the composition compositor, the pullback map, and
the canonical tensor comparison, then use functoriality of localization. Endpoint
normalization identifies the resulting morphisms with the displayed types.
-/
theorem canonicalRationalPullbackTensorComposition_right_localization {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfRationalConstructibleCategory l E Y) :
    HEq
      ((pullbackTensorRationalComposition l E f h
          ((rationalDerivedTensor l E Y).obj (M,N))).hom ≫
        (rationalDerivedPullback l E h).map
          (canonicalRationalPullbackTensor l E f M N).hom ≫
        (canonicalRationalPullbackTensor l E h
          ((rationalDerivedPullback l E f).obj M)
          ((rationalDerivedPullback l E f).obj N)).hom)
      ((sfRationalConstructibleLocalization l E Z).map
        ((pullbackTensorIntegralComposition l E f h).hom.app
            ((constructibleIntegralTensor l E Y).obj (M.obj,N.obj)) ≫
          (constructibleIntegralPullback l E h).map
            (canonicalIntegralPullbackTensor l E f M.obj N.obj).hom ≫
          (canonicalIntegralPullbackTensor l E h
            ((constructibleIntegralPullback l E f).obj M.obj)
            ((constructibleIntegralPullback l E f).obj N.obj)).hom)) := by
  sorry

end WeilConjectures
