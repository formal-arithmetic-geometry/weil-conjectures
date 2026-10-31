/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralImmersionNormalization.IntegralImmersionPullbackNormalizationData

/-! # Compatibility of normalized integral immersion pullbacks -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
namespace WeilConjectures.IntegralImmersionNormalization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : Y ⟶ X) [IsImmersion g]

/-- The prescribed integral and completion comparisons respect the same completed
shift, with the canonical ordinary shift and the specified integral shift.
Source: Stacks proetale.tex, Tags 09AA and 099N; sites-cohomology.tex, Tag 0941
(blueprint: lem-sf-integral-immersion-shift-compatibility).

Proof: inverse image for an immersion is exact and commutes with countable
products. Compute its strict derived limit by the normalized Roos comparison.
The completion-unit augmentation has coordinates (0,(x mod t^n)_n), and the
Roos shift sends (y,x) to ((-1)^r y,x). Consequently this augmentation commutes
with every integer shift, including zero and addition. Transport through the
normalized exact coefficient restrictions and their identity-on-sections round
trip gives shift compatibility for c. For gamma use C.shifts and the
unit-normalized strict/reflector comparison: both are represented by the same
finite quotient maps and the same signed Roos shift. Their intertwining squares
compose to the displayed square for gamma. Naturality of the round trip gives
the source correction in its normalization formula. These equations define the
same completed shift because the Roos realization is fixed before restriction
to constructible objects; no shift is chosen independently for the two maps. -/
theorem immersion_comparison_shifts
    (C : IntegralCompletedComparison.Comparison l E g)
    (hc : ∀ K : sfIntegralConstructibleCategory l E X,
      IntegralCompletedComparison.Complete l E ((back l E X).obj K.obj))
    (γ : (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E g ≅
      (sfIntegralConstructible l E X).ι ⋙ completed l E g)
    (hγ : ∀ K : sfIntegralConstructibleCategory l E X,
      γ.hom.app K =
        (integralDerivedPullback l E g).map ((roundTrip l E X).inv.app K.obj) ≫
        (C.gamma ((back l E X).obj K.obj) (hc K)).hom ≫
        (ImmersionCompletedPullback.transport l E Y).map
          ((IntegralCompletedComparison.towerIso l E g).inv.app
            ⟨(back l E X).obj K.obj, C.intrinsic ((back l E X).obj K.obj) (hc K)⟩))
    (c : (sfIntegralConstructible l E X).ι ⋙ ordinary l E g ≅
      (sfIntegralConstructible l E X).ι ⋙ completed l E g)
    (hc' : c.hom = whiskerLeft (sfIntegralConstructible l E X).ι
      (completionComparison l E g)) :
    ∃ sc : (completed l E g).CommShift ℤ,
      (fun [_si : (integralDerivedPullback l E g).CommShift ℤ]
        [_sc : (completed l E g).CommShift ℤ] ↦ NatTrans.CommShift γ.hom ℤ)
          (_si := C.derivedShift) (_sc := sc) ∧
      (fun [_sc : (completed l E g).CommShift ℤ] ↦ NatTrans.CommShift c.hom ℤ)
        (_sc := sc) := by sorry

end WeilConjectures.IntegralImmersionNormalization
