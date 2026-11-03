/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Open-immersion normalization of condensed smooth purity

The coefficient-unit, relative-dimension-zero instance of `sk-thm-purity-transport`.
Source: the current blueprint, smooth purity transport, Step 3
(blueprint: lem-route-smooth-purity-iso-zero-of-is-open-immersion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- The specified smooth purity isomorphism of an open immersion agrees with the
counit-compatible exceptional pullback comparison, followed by the inverse zero
Tate-twist and zero-shift comparisons. This is the algebraic-closure coefficient,
unit-input instance of all-coefficient smooth purity.

Source: current blueprint `sk-thm-purity-transport`, Step 3, with the finite
étale normalization and the integral/scalar construction in Steps 1--2
(blueprint: lem-route-smooth-purity-iso-zero-of-is-open-immersion).

Proof: Use the compactification-independence comparison to express the chosen
lower shriek in ordinary open-extension-by-zero coordinates. At each finite
coefficient level the diagonal/DNC adjunction at dimension zero is the ordinary
étale adjunction, including its actual counit. The diagonal tower evaluations
therefore identify the normalized inverse orientation with the open unit map:
both sides are degree-zero tower morphisms, so equality is componentwise by full
faithfulness of the single-complex embedding. The whole-tower integral counit
comparison and full faithfulness of integral reduction give the same equality
before scalar extension. Extend scalars to the finite-extension-valued condensed
algebraic closure. The open scalar mate preserves the counit and coefficient
unit; its refinement-pasting identity transports the calculation from the trivial
to the chosen compactification. Consequently the smooth trace is exactly the
ordinary open counit precomposed with the zero-twist/zero-shift comparisons.
Taking adjoints gives alpha = beta inverse composed with those comparisons.
Invert this equality and apply the full inclusion into the ambient derived
category; the three factors appear in the displayed order. -/
theorem smoothPurityIso_zero_of_isOpenImmersion_finite_or_algClosed
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (_hk : Finite k ∨ IsAlgClosed k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (j : X ⟶ Y) [IsOpenImmersion j.left] :
    smoothPurityIso ℓ j 0 =
      (ObjectProperty.ι _).mapIso (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j) ≪≫
        (tateTwistDerivedZeroIso ℓ X.left).symm ≪≫
        ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).symm := by
  exact smoothPurityIso_zero_of_isOpenImmersion ℓ j

end AlgebraicGeometry.ProEtale.CondensedRing
