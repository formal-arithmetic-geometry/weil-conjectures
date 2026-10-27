/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.Paper.PbcCompletedPullbackActual
public import Sheaf.Paper.CompletedPullbackInterface
import all Sheaf.Paper.PbcCompletedPullbackActual

/-! # Actual completion and quotient completion

Source: Stacks 099M and 099N.
(blueprint: lem-sfb-integral-roos-completion-reflector-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralPullbackStrictRoos

/-- Actual intrinsic completion and quotient-tower completion agree with their units.

Source: Stacks 099M, 099N; the existing private actualCompletion_quotient proof in
PbcCompletedPullbackActual.
(blueprint: lem-sfb-integral-roos-completion-reflector-comparison).

Proof: choose finite generators of the coefficient ideal. The Koszul-to-quotient
comparison identifies the explicit Koszul reflector with the entire quotient-tower
completion, carrying its augmentation to the quotient unit. Transfer the complete-output
property and the Hom bijection to that functor. The actual intrinsic-complete
subcategory reflector has the same reflection property. The unique maps between the
two reflection objects commute with the units, are mutually inverse by uniqueness,
and are natural by the same Hom bijection. This gives the asserted natural isomorphism.
The construction works for every input, without assuming input completeness. -/
theorem integralRoosCompletionReflectorComparison
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (S : Scheme.{u}) :
    ∃ e : pbcActualCompletion d S ≅
        completedReductionTower S d ⋙ completedRlim S (d.completedRing S),
      ∀ M, (pbcActualCompletionUnit d S).app M ≫ e.hom.app M = d.completionUnit S M := by
  exact actualCompletion_quotient d S

end WeilConjectures.IntegralPullbackStrictRoos
