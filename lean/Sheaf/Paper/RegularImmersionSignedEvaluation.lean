/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.PurityConventions
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
public import Sheaf.Paper.PurityFrameClass
import Sheaf.Paper.PurityFrameIndependence
public import Sheaf.Paper.SupportedCupFunctoriality
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

public import Sheaf.Paper.RegularImmersionClassData
/-!
# Signed shifted Tate evaluation and pullback

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-regular,
signed Tate evaluation
(blueprint: def-pur-regular-immersion-signed-evaluation).

All coefficients are the actual finite quotient of the fixed purity setting. Supported
classes use the published Hom model, and their restriction uses the section-normalized
closed coefficient exchange. The frame product is the existing ordered Kummer-boundary fold.

## Main declarations

* `regularEvaluation`.
* `regularSignedPullback`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u u'

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- The existing signed finite Tate sheaf, in fixed-scalar pro-etale coordinates.
Source: coefficient twists (blueprint: def-pur-regular-immersion-signed-evaluation). -/
def regularSignedSheaf (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (r : ℤ) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient) :=
  (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj
    (Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
      P.diagonalExponent_annihilates r)

/-- Evaluation of a positive Tate line against its specified negative dual.
Source: the inverse Tate shift (blueprint: def-pur-regular-immersion-signed-evaluation). -/
def regularEtaleEvaluation (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    (c : ℕ) → P.frameTwistEtale X c ⊗
      Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
        P.diagonalExponent_annihilates (-(c : ℤ)) ⟶ P.constantEtale X
  | 0 => (λ_ (P.constantEtale X)).hom
  | c + 1 => (ihom.ev (P.frameTwistEtale X (c + 1))).app (P.constantEtale X)

/-- The duality evaluation after the actual strong monoidal site comparison.
Source: inverse Tate shifts (blueprint: def-pur-regular-immersion-signed-evaluation). -/
def regularSheafEvaluation (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (c : ℕ) :
    P.frameTwist X c ⊗ P.regularSignedSheaf X (-(c : ℤ)) ⟶ P.constant X :=
  (asIso (Functor.OplaxMonoidal.δ
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X)
    (P.frameTwistEtale X c)
    (Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
      P.diagonalExponent_annihilates (-(c : ℤ))))).inv ≫
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
      (P.regularEtaleEvaluation X c)

/-- The opposite Tate shifts have sum zero.
Source: cancellation of shifts (blueprint: def-pur-regular-immersion-signed-evaluation).
Proof: multiplication by two preserves the additive inverse in the integers. -/
theorem regularCancelDegree (c : ℕ) : 2 * (c : ℤ) + 2 * (-(c : ℤ)) = 0 := by
  sorry

/-- The canonical shifted evaluation in the native generic API carrier.
Source: cancelling the invertible twist in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-signed-evaluation). -/
def regularNativeEvaluation (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (c : ℕ) :=
  regularEvaluationCanonical
    (P.frameTwist X c) (P.regularSignedSheaf X (-(c : ℤ))) (P.constant X)
    (2 * (c : ℤ)) (2 * (-(c : ℤ))) (regularCancelDegree c) (P.regularSheafEvaluation X c)

/-- The displayed shifted-Tate evaluation Hom, with its canonical tensor structure.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-signed-evaluation). -/
def regularEvaluationTarget (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (c : ℕ) : Type _ :=
  P.regularTate X c ⊗ P.regularTate X (-(c : ℤ)) ⟶
    (P.regularSingle X).obj (P.constant X)

/-- The native shifted-evaluation carrier is the displayed Tate-evaluation Hom.
Source: opposite Tate shifts in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-signed-evaluation).
Proof: rewrite the shared tensor structure by regularTensorMonoidal_eq, then expand
regularTate and the common single-functor references. The two Hom types have identical
objects, shifts and localization structures. -/
theorem regularEvaluationHom_eq (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (c : ℕ) :
    (type_of% (P.regularNativeEvaluation X c)) =
      P.regularEvaluationTarget X c := by
  sorry

/-- Evaluation A(c)[2c] tensor A(-c)[-2c] to A, using the published tensor-shift
comparison, degree-zero tensor localization, and the actual dual evaluation.
Source: cancelling the invertible twist
(blueprint: def-pur-regular-immersion-signed-evaluation). -/
def regularEvaluation (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (c : ℕ) :
    P.regularEvaluationTarget X c :=
  cast (P.regularEvaluationHom_eq X c) (P.regularNativeEvaluation X c)

/-- The canonical signed shifted-Tate pullback, through the root/dual-normalized
ordinary inverse image and the exact derived/single and shift comparisons.
Source: cancelling a Tate shift through Ri!
(blueprint: def-pur-regular-immersion-signed-evaluation). -/
def regularSignedPullback (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (r : ℤ) :=
  regularExactPullbackShift (ModuleCat.{u + 1} P.Coefficient) i
    (P.regularSignedSheaf X r) (P.functorialCupTwist true Z r)
    (P.functorialCupTwistPullback true i aX r) (2 * r)


end WeilConjectures.PurityFiniteSetting
