/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.Paper.ProEtaleConstantReductionTower

/-! # Strict quotient augmentation and the prescribed pullback comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange

/-- The normalized reduction/pullback isomorphism carries the strict quotient
augmentation to the quotient augmentation after pullback.

Source: Stacks 07A4, 099M; the strict augmentation square in step 4 of
lem-cbc-completed-support-intermediate-tower. It is the pullback square underlying
lem-pur-strict-reduction-projection-completion-unit, here in the prescribed
pro-etale constant-coefficient realization.

Proof: on ordinary modules, the quotient augmentation inserts `1 tensor x`.
The ordinary reduction/pullback isomorphism is the normalized scalar-change map;
it sends the pullback of `1 tensor x` to `1 tensor pullback(x)`. The diagonal
comparison is the identity on the termwise pullback. Thus the square commutes
at every level, and the equations commute with quotient transitions, which are
induced by the quotient ring maps and preserve `1`. This is an equality of
ordinary strict tower maps, not just a family of equalities in derived categories.
Apply the functors on cochain and homotopy categories to this square. Compute
reduction on flat-term K-flat representatives whose pullbacks remain K-flat.
The universal reduction counits and the representative normalization of
`reductionPullIso` identify the localized square with the displayed one;
`augmentation_normalized` identifies its two augmentation edges. The resolving
class localization property extends equality from these representatives to the
whole derived category. This retains the specified comparisons and all strict
transitions. The same calculation applies to the identity morphism, zero complex,
empty schemes, and the zero or unit ideal; it uses no completeness hypothesis.
(blueprint: lem-cbc-support-reduction-augmentation-pull). -/
theorem supportReductionAugmentationPull {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {U Y : Scheme.{t}} (p : U ⟶ Y) :
    whiskerRight (augmentation d Y) (exchangeConstantPull (A := A) p) ≫
        (reductionPullIso d p).hom =
      (diagonalPullIso (A := A) p).hom ≫
        whiskerLeft (pull (A := A) p) (augmentation d U) := by
  sorry

end AlgebraicGeometry.Scheme.OrderedExchange
