/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealization
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
import WeilConjectures.SmoothPurity.Integral.IntegralCanonicalPullbackTensorReduction
import WeilConjectures.SmoothPurity.Integral.IntegralSystemCompositionIdentification

/-! The reduced system form of integral pullback/tensor composition coherence.

Source: Stacks 07A4 and 0941; the strict quotient-system calculation before reflection.
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced)

The former finite-evaluation proof used a false joint-faithfulness assertion.
`integralPullbackTensorCompositionReduced_of_systemLaw` compares whole strict-system
representatives before localization: for every compositor whose reduction is the system
compositor after the whole-system pullback comparisons, the equation reduces to the
composition law of the coherent system pullback/tensor comparison, which descends from
the strict cochain law. The compositor of `integralPullbackComposition_systemNormalized`
has this normalization. The recorded compositor `pullbackTensorIntegralComposition` is
chosen from `integralPullbackComposition`, whose statement only pins finite evaluations,
so the named theorem below remains open.
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

set_option maxHeartbeats 4000000 in
-- Matching the transported system law and the reduced comparisons unfolds the two
-- presentations of the coherent derived system categories.
/-- Reduced integral pullback/tensor composition equation for a system-normalized compositor.
Source: Stacks 07A4 and 0941; quotient-system pure-tensor calculation.
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced)

Proof: the reductions of the canonical integral pullback/tensor comparisons are the
system comparisons conjugated by the whole-system pullback comparisons of
`integralPullbackSystemComparison_realization` and the reduction/tensor comparisons.
The system comparisons obey the composition law for the system compositor, by descent of
the strict cochain law. The hypothesis on `c` identifies its reduction with the system
compositor; `reducedPullbackTensorComposition_of_systemLaw` combines these equations. -/
theorem integralPullbackTensorCompositionReduced_of_systemLaw {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (c : constructibleIntegralPullback l E (h ≫ f) ≅
      constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E h)
    (hc : ∀ K : sfIntegralConstructibleCategory l E Y,
      (integralSystemReduction l E Z).map (c.hom.app K) ≫
          ((integralPullbackSystemComparison_realization l E).choose h).hom.app
            ((constructibleIntegralPullback l E f).obj K) ≫
          (finiteSystemDerivedPullback (integralSystemRings l E)
            (integralSystemTransition l E) h).map
              (((integralPullbackSystemComparison_realization l E).choose f).hom.app K) =
        ((integralPullbackSystemComparison_realization l E).choose (h ≫ f)).hom.app K ≫
          (finiteSystemDerivedComposition (integralSystemRings l E)
            (integralSystemTransition l E) h f).hom.app
              ((integralSystemReduction l E Y).obj K))
    (M N : sfIntegralConstructibleCategory l E Y) :
    (integralSystemReduction l E Z).map
        ((canonicalIntegralPullbackTensor l E (h ≫ f) M N).hom ≫
          (constructibleIntegralTensor l E Z).map
            (Prod.mkHom (c.hom.app M) (c.hom.app N))) =
      (integralSystemReduction l E Z).map
        (c.hom.app ((constructibleIntegralTensor l E Y).obj (M, N)) ≫
          (constructibleIntegralPullback l E h).map
            (canonicalIntegralPullbackTensor l E f M N).hom ≫
          (canonicalIntegralPullbackTensor l E h
            ((constructibleIntegralPullback l E f).obj M)
            ((constructibleIntegralPullback l E f).obj N)).hom) := by
  refine reducedPullbackTensorComposition_of_systemLaw
    (integralSystemReduction l E Y) (integralSystemReduction l E X)
    (integralSystemReduction l E Z)
    (constructibleIntegralPullback l E f) (constructibleIntegralPullback l E h)
    (constructibleIntegralPullback l E (h ≫ f))
    (finiteSystemDerivedPullback (integralSystemRings l E) (integralSystemTransition l E) f)
    (finiteSystemDerivedPullback (integralSystemRings l E) (integralSystemTransition l E) h)
    (finiteSystemDerivedPullback (integralSystemRings l E) (integralSystemTransition l E)
      (h ≫ f))
    (constructibleIntegralTensor l E Y) (constructibleIntegralTensor l E X)
    (constructibleIntegralTensor l E Z)
    (pullbackTensorCalculus l E Y).systemClosed.tensor
    (pullbackTensorCalculus l E X).systemClosed.tensor
    (pullbackTensorCalculus l E Z).systemClosed.tensor
    ((integralPullbackSystemComparison_realization l E).choose f)
    ((integralPullbackSystemComparison_realization l E).choose h)
    ((integralPullbackSystemComparison_realization l E).choose (h ≫ f))
    (integralSystemTensorReduction l E Y) (integralSystemTensorReduction l E X)
    (integralSystemTensorReduction l E Z)
    (integralSystemTensorComparison l E f) (integralSystemTensorComparison l E h)
    (integralSystemTensorComparison l E (h ≫ f))
    (finiteSystemDerivedComposition (integralSystemRings l E) (integralSystemTransition l E) h f)
    c hc
    (canonicalIntegralPullbackTensor l E f) (canonicalIntegralPullbackTensor l E h)
    (canonicalIntegralPullbackTensor l E (h ≫ f))
    ?_ ?_ ?_ ?_ M N
  · exact canonicalIntegralPullbackTensor_systemReduction l E f
  · exact canonicalIntegralPullbackTensor_systemReduction l E h
  · exact canonicalIntegralPullbackTensor_systemReduction l E (h ≫ f)
  · intro A B
    have hσ := integralSystemTensorComparison_comp l E h f A B
    rw [← finiteSystemDerivedComposition_eq] at hσ
    exact hσ

/-- The reduced pullback/tensor composition equation holds for the system-normalized
compositor of `integralPullbackComposition_systemNormalized`.
Source: Stacks 07A4 and 0941
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).
Proof: its third clause is the hypothesis of
`integralPullbackTensorCompositionReduced_of_systemLaw`. -/
theorem integralPullbackTensorCompositionReduced_systemNormalized {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    (integralSystemReduction l E Z).map
        ((canonicalIntegralPullbackTensor l E (h ≫ f) M N).hom ≫
          (constructibleIntegralTensor l E Z).map
            (Prod.mkHom
              (((integralPullbackComposition_systemNormalized l E).choose h f).hom.app M)
              (((integralPullbackComposition_systemNormalized l E).choose h f).hom.app N))) =
      (integralSystemReduction l E Z).map
        (((integralPullbackComposition_systemNormalized l E).choose h f).hom.app
            ((constructibleIntegralTensor l E Y).obj (M, N)) ≫
          (constructibleIntegralPullback l E h).map
            (canonicalIntegralPullbackTensor l E f M N).hom ≫
          (canonicalIntegralPullbackTensor l E h
            ((constructibleIntegralPullback l E f).obj M)
            ((constructibleIntegralPullback l E f).obj N)).hom) :=
  integralPullbackTensorCompositionReduced_of_systemLaw l E f h _
    (fun K ↦ (integralPullbackComposition_systemNormalized l E).choose_spec.2.2 h f K) M N

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
For the system-normalized compositor the equation is
`integralPullbackTensorCompositionReduced_systemNormalized`. The remaining step is to
identify `pullbackTensorIntegralComposition`, the compositor chosen from the statement of
`integralPullbackComposition`, with a system-normalized one: that statement only fixes
its finite evaluations, which do not determine a map of complete objects (lim¹ terms).
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
