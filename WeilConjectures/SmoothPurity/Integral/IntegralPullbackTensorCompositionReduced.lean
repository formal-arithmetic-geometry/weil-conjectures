/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealization
import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition

/-! The reduced system form of integral pullback/tensor composition coherence.

Source: Stacks 07A4 and 0941; the strict quotient-system calculation before reflection.
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced)

The former finite-evaluation proof used a false joint-faithfulness assertion.
This module retains the required specific equation as an open named theorem.
The repair must compare whole strict-system representatives before localization.
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
Source: Stacks 07A4 and 0941; quotient-system pure-tensor calculation.
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced)

Proof plan: resolve the two inputs simultaneously by flat-term K-flat complexes
and form their strict quotient systems. Use the unit-normalized system pullback
compositor, before localization. On every total-tensor summand the two routes
send a pure tensor to the pair of its pulled-back factors; balancing identifies
these chain maps, including their horizontal transition maps. Localize this
single equality of whole systems. Transport along the coherent reduction/tensor
and reduction/pullback comparisons and cancel their invertible components.
The normalization of the recorded integral compositor must identify it with this
coherent compositor on representatives; its finite-evaluation formula alone does
not establish that identification. Expose or repair that normalization before
using it here. Then the transported equality is precisely the displayed equation.
No inference from separate finite derived evaluations is used.

This restores the obligation hidden by the invalid extensionality split; it does
not assert that the required whole-system normalization has already been proved.
-/
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
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom) := by sorry

end WeilConjectures
