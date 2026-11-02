/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-! # Direct condensed point fibres and finite reduction

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sfb-proper-base-change/def-weil-finite-coefficient-point.md, the four equivalences;
sec-six-functors-basics/sk-prop-qlbar-two-colimit/det-def-sf-operations.md; and
sec-smooth-purity/sk-lem-sp-reduction/thm-pur-finite-reduction-of-purity.proof.md, Step 2
(blueprint: def-weil-point-fibre-stage-constructions).

The point equivalences below restrict the actual derived final-section evaluation and
its scalar realization. Their scalar target is the ordinary derived category of the
section ring, including at Qbar. The publicly imported six operations are the direct
operations on modules over `condensedRingObj Λ T = p_T^* Λ`: `moduleObjectDerivedPullback`,
`derivedTensor`, `derivedHom`, `moduleObjectDerivedPushforward`,
`rightDerivedLowerShriekOfCompactification`, and `ctfExceptionalInverseImage`.
The last operation is the finite-Tor restriction of the localizing Brown right adjoint,
not an assumed ambient right adjoint. No integral or rational operation is defined here
by reduction or by a category of coefficient representatives.

The finite part uses the existing intrinsic constant-ring coordinates of
`PurityFiniteSetting`, exactly as do the recorded root-chart and comparison nodes.
`finiteTorReduction` restricts their actual derived extension along the quotient
O_E/(pi^n) -> O_E/(pi^m). The five canonical comparisons are publicly reexported unchanged:
`finiteReductionPullbackComparison`, `finiteReductionSourceComparison`,
`finiteReductionCompactSupportComparison`, `finiteReductionExceptionalComparison`,
and `finiteReductionUnitComparison`. Their normalization and invertibility
on the stated domains are supplied by their owning dependency module. The naturality
statements below package these fixed components as natural isomorphisms; no commutativity
of purity, orientation, trace, composition or base-change squares is asserted.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedGeometricPoint

end AlgebraicGeometry.ProEtale.CondensedGeometricPoint

namespace WeilConjectures.PurityFiniteSetting

section Comparisons

variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The natural pullback comparison has precisely the canonical mate as its components.
Source: finite-reduction-of-purity, Step 2
(blueprint: def-weil-point-fibre-stage-constructions). -/
def pointReductionPullbackIso :
    (finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y).ι ⋙
        P.finiteReductionPullback f ⋙ P.finiteReduction m hm hmn X ≅
      (finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y).ι ⋙
        P.finiteReduction m hm hmn Y ⋙
          (P.finiteReductionSetting m hm).finiteReductionPullback f :=
  NatIso.ofComponents (fun K ↦ P.finiteReductionPullbackComparison m hm hmn f K.obj)
    (fun a ↦ P.pointReductionPullback_naturality m hm hmn f a)

end Comparisons

end WeilConjectures.PurityFiniteSetting
