/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralSystemReductionFullyFaithful
public import Sheaf.Paper.DerivedPullbackTensorConstraints

/-! Finite coefficient stages of the reduced integral pullback/tensor equation.

Source: Stacks 07A4 and 0941; pure tensor calculation on each positive quotient
of the normalized coefficient tower.
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced-finite-stage)

The proof is intentionally split from the tower-level statement.  At one
quotient, choose flat-term K-flat representatives.  Both composites send a
pure tensor to the same pulled-back pair, and the formula commutes with the
transition maps.  The resulting equality descends through localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- The reduced pullback/tensor composites agree after every finite evaluation.

Source: Stacks 07A4 and 0941, quotient-stage pure-tensor calculation.
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced-finite-stage)

At a positive coefficient quotient, the two displayed maps are represented by
identical pure-tensor formulas on flat-term K-flat representatives.  These
formulas commute with quotient transitions, so localization gives the stated
morphism equality.  This is the finite-stage part of the quotient-tower
argument; the tower extensionality step is recorded separately.
-/
theorem integralPullbackTensorCompositionReduced_finiteStage
    {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfIntegralConstructibleCategory l E Y) (n : ℕ) :
    (finiteSystemDerivedEvaluation (integralSystemRings l E)
        (integralSystemTransition l E) Z n).map
        ((integralSystemReduction l E Z).map
          (((@canonicalIntegralPullbackTensor l _ E _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
            ((@constructibleIntegralTensor l _ E _ _ _ Z hZ)).map (Prod.mkHom
              (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app M)
              (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app N)))) =
      (finiteSystemDerivedEvaluation (integralSystemRings l E)
        (integralSystemTransition l E) Z n).map
        ((integralSystemReduction l E Z).map
          (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app
            (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (M, N)) ≫
            ((@constructibleIntegralPullback l _ E _ _ _ Z X h hZ hX)).map
              ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
            ((@canonicalIntegralPullbackTensor l _ E _ _ _ Z X h hZ hX)
              (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
              (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom)) := by
  sorry

end WeilConjectures
