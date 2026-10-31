/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionTensorFactors

/-! # Agreement of the two normalized positive-line reduction maps

Source: blueprint/latest, thm-pur-finite-reduction-of-purity, Steps 2–3.
(blueprint: lem-pur-finite-reduction-positive-line-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
open Etale.FiniteSmoothPurity FiniteDiagonalReduction

/-- The root-power comparison used for the diagonal agrees with the positive-line
comparison used by the tensor-source map. This concerns only coefficient lines.
Source: blueprint/latest reduction Steps 2–3, comparison of the normalized root maps
(blueprint: lem-pur-finite-reduction-positive-line-comparison).
Proof: choose a primitive root at level P.level, and its specified power at m.
The roots_power equation fixes the root arrow since the kernel inclusion is mono.
The generators equation therefore identifies sheafIso with scalar balancing of
the quotient root-power map. The derived_normalization equation identifies its
derived arrow with the scalar counit on that single flat line. At d=0 the scalar
unit map is the same multiplication map, with inverse b maps to b tensor 1.
For d+1 the tensorPower recursion uses the binary scalar tensorator and canonical
shift. The normalization of finiteTensorCore identifies this with its K-flat
representative tensorator; the normalization of finiteTensorLineComparison gives
the same scalar-balanced product of generators. Induction gives equality on all
ordered positive powers and shifts. The defining primitive-root equations for
finiteTensorPositivePresentation conjugate this equality into diagonalTwist.
The site/scalar comparison and intrinsic scalar presentation are the mates of the
same sectionwise restriction square, so their units and counits cancel. This is
exactly the asserted equality, for arbitrary ramification, m=P.level and d=0. -/
theorem finiteReduction_positiveLineComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))] (d : ℕ)
    (e : CoefficientLineComparison (quotient P m hm hmn)
      P.diagonalExponent (P.finiteReductionSetting m hm).diagonalExponent
      P.diagonalExponent_annihilates
      (P.finiteReductionSetting m hm).diagonalExponent_annihilates X) :
    proTwistMap d e = (P.finiteTensorPositiveReduction m hm hmn X d).hom := by sorry

end WeilConjectures.PurityFiniteSetting
