/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedPullbackTensorConstraints
public import Sheaf.Paper.IntegralSystemReductionFullyFaithful
import Sheaf.Paper.CompletedComparisonQuotientRealization
import Sheaf.Paper.IntegralPullbackComposition

/-! The reduced system form of integral pullback/tensor composition coherence.

Source: Stacks 07A4 and 0941; the quotient-tower calculation before reflection.
(blueprint: lem-pur-pullback-tensor-integral-composition-coherence)

The equality is checked on the normalized finite quotient tower.  The completed
comparison and the integral pullback compositor are both represented by the
same pure-tensor map at every quotient stage; transition compatibility makes
these maps equal in the finite-system derived category.
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
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- Reduced form of the integral pullback/tensor composition equation.
Source: Stacks 07A4 and 0941; the quotient-tower pure-tensor calculation.
(blueprint: lem-pur-pullback-tensor-integral-composition-coherence)

The normalized quotient-tower representatives of both sides are identical at
every finite coefficient level.  Their transition maps commute with the
pure-tensor pullback formula, so the induced maps in the finite-system derived
category are equal. -/
theorem integralPullbackTensorCompositionReduced {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    (integralSystemReduction l E Z).map
        (((@canonicalIntegralPullbackTensor l _ E _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
          ((@constructibleIntegralTensor l _ E _ _ _ Z hZ)).map (Prod.mkHom
            (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app M)
            (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app N))) =
      (integralSystemReduction l E Z).map
        (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app
          (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (M, N)) ≫
          ((@constructibleIntegralPullback l _ E _ _ _ Z X h hZ hX)).map
            ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
          ((@canonicalIntegralPullbackTensor l _ E _ _ _ Z X h hZ hX)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom) := by
  sorry

end WeilConjectures
