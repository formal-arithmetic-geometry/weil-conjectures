/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.FunctionField
import Sheaf.AlgebraicGeometry.IntegralPushforwardBaseChangeArrow
import Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection
import Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeQuotientDetection
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity.CriticalMap
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange

/-!
# Universal curve-test data with a signed annihilator

Source: current blueprint, sec-smooth-base-change/sk-lem-universal-datum/_section.md;
Stacks Project, Tag 0F08 (blueprint: sk-lem-universal-datum).

The existing `Etale.CurveTestDatum` supplies the geometry and coefficient sheaf. The integer
annihilator here retains the source's signed convention. Its absolute value supplies the
natural-number annihilator of the upstream theorem. The nonnegative witness `D.d`, read as
an integer, loses no existential case: changing the sign of a generator leaves its ideal
and its constant quotient sheaf unchanged.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Universal curve-test datum for a failure, with the source's signed integer annihilator.
Source: current blueprint, sec-smooth-base-change/sk-lem-universal-datum/_section.md;
Stacks Project, Tag 0F08 (blueprint: sk-lem-universal-datum).

Proof plan. Apply `sk-lem-failure-field` to obtain an affine-base failure over a field;
affine qcqs and qcqs permanence make its test morphism qcqs. Replace the field by an
algebraic closure. The contrapositive of `lem-sbc-module-bc-integral-surjective` preserves
failure, using the fixed-base lower-degree property. Apply
`lem-sbc-normalization-algclosed-field` to obtain an affine integral normal base with
algebraically closed function field and a geometric generic point. Failure persists by
`lem-sbc-integral-pushforward-base-change-arrow` and the exact, isomorphism-reflecting
coefficient comparisons of `lem-weil-pbc-exchange-forget-coefficients`.

Universality supplies the lower-degree hypothesis for this base change.
`lem-sbc-module-bc-injectivity` makes the failed degree-q arrow monic, so its target is
nonzero. The map h is qcqs as a base change of the geometric generic point, by
`lem-weil-pbc-qcqs-morphism-permanence`. The integer n is nonzero since it pulls back to a
unit in the nonzero field. Put N = |n|. The coefficient target is the higher direct image
of the inverse image by `sbc-def-base-change-map`. Apply `lem-sbc-prime-cyclic-detection`
to N, then the contrapositive of `lem-sbc-prime-quotient-detection`, obtaining a prime d
with nonzero higher direct image of the constant quotient by d. Its divisibility of N
gives integer divisibility of n. Pull back the unit n; if n = d t, then t/n is an inverse
for d on the new base. Affine and smooth-relative-dimension permanence supply the curve
geometry (`lem-weil-pbc-affine-morphism-permanence` and
`lem-sbc-smooth-relative-dimension-permanence`). Package it in the existing curve-test
datum; the outer pullback has its canonical chosen fibre-product identification. -/
theorem Etale.exists_curveTestDatum_of_int (Λ : Type (u + 1)) [CommRing Λ]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffineHom f]
    [SmoothOfRelativeDimension 1 f] (n : ℤ) (hn : IsUnit (n : Γ(S, ⊤)))
    (hΛ : (n : Λ) = 0) (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ q' : ℤ, q' ≤ q - 1 → Etale.UniversalBaseChangeProperty Λ f q')
    (hfail : ¬ Etale.BaseChangeProperty Λ f q) :
    ∃ (D : Etale.CurveTestDatum.{u}) (a : D.S₀ ⟶ S) (b : D.X₀ ⟶ X)
      (_ : ChosenCartesianSquare b D.f₀ f a),
      (D.d : ℤ) ∣ n ∧
      ¬ IsZero (Etale.higherDirectImage Λ D.h q (Etale.constantModSheaf Λ D.Y₀ D.d)) := by
  sorry

end AlgebraicGeometry
