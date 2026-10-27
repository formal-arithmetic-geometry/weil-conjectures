/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Sheaf.Paper.FiniteTensorSignedReduction
public import Sheaf.Paper.FinitePositiveRootCharts

/-! # Scalar reduction of the unshifted positive root charts

Source: blueprint/latest, finite reduction of purity, Step 2, and the parent
finite tensor presentation reduction, Step 8; Stacks Tags 03EK and 07A4.
(blueprint: lem-pur-finite-tensor-line-chart-reduction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

/-- The signed-line comparison preserves compatible unshifted positive root charts.
Source: blueprint/latest, thm-pur-finite-reduction-of-purity, Step 2; parent
lem-pur-finite-tensor-presentation-reduction, Step 8; Stacks 03EK and 07A4.
(blueprint: lem-pur-finite-tensor-line-chart-reduction).
Proof: lift ζ to a compatible sequence of primitive ℓ-power roots. Its coordinate
at m is η by hroot. Trivialize the integral rank-one line using this sequence.
The degree-one balancing normalization of finiteTensorLineMaps sends its reduced
A-basis to the reduced B-basis. The positive tensor recursion therefore sends
all ordered d-fold basis tensors to their B-counterparts. Both ordinary root
charts send these basis tensors to 1. In degree zero the semilinear map is the
coefficient ring map. The normalized tensorator and its unit axiom identify the
core unit inverse with scalar multiplication, so the assertion holds for d = 0
as well. These are equations of ordinary sheaf maps, checked on generators after
local trivialization and then glued. Apply the exact single-complex functor and
the scalar adjunction. Its hom equivalence is injective, and the recorded adjoint
normalization of finiteTensorLineComparison identifies the two transposes with
these same ordinary maps. This proves the derived equality without testing
arbitrary derived arrows locally. Changing the integral lift fixes the finite
basis at level n and therefore at level m, so the calculation is independent of
the lift. It applies to m = P.level, the empty scheme, and ramified coefficients;
no flatness of the quotient map is used. -/
theorem finiteTensorLineChart_reduction (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (d : ℕ) (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (η : P.field.k)
    (hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent)
    (hroot : η = ζ ^ (P.coefficients.l ^ (P.level - m))) :
    (P.finiteTensorLineComparison m hm hmn T d).hom ≫
        ((P.finiteReductionSetting m hm).finiteTensorPositiveChart T η hη d).hom =
      (P.finiteTensorReduction m hm hmn T).map
          (P.finiteTensorPositiveChart T ζ hζ d).hom ≫
        (P.finiteTensorCore m hm hmn T).εIso.inv := by sorry

end WeilConjectures.PurityFiniteSetting
