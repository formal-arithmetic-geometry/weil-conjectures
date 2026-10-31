/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientData
import WeilConjectures.AlgebraicGeometry.FiniteFreeRestrictionDirectImageMate

/-! # Finite proper coefficient comparison invertibility

Source: Stacks Tags 0GL5 and 0GL6.
(blueprint: lem-pur-compact-support-finite-proper-comparison-iso).

This lower statement isolates invertibility of the proper factor of the finite
coefficient comparison; the parent comparison theorem combines it with the
open factorization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport

/-- The proper scalar mate is invertible for the finite coefficient change.
Source: Stacks Tags 0GL5 and 0GL6.
(blueprint: lem-pur-compact-support-finite-proper-comparison-iso).
Proof: finite freeness identifies the scalar restriction square with a finite
biproduct comparison; proper direct image preserves the resulting isomorphism,
and the adjunction mate preserves invertibility. -/
def finiteProperComparison {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    proEtaleRingDerivedDirectImage g (R.ring V) (R.ring U) (R.pull g) ⋙
        pbcDerivedExtend (a.map V) ⟶
      pbcDerivedExtend (a.map U) ⋙
        proEtaleRingDerivedDirectImage g (S.ring V) (S.ring U) (S.pull g) :=
  ((mateEquiv (pbcDerivedScalarAdjunction (a.map U))
    (pbcDerivedScalarAdjunction (a.map V))).symm
      (TwoSquare.mk _ _ _ _
        (proEtaleRingRestrictionDerivedDirectImage g
          (R.ring V) (S.ring V) (R.ring U) (S.ring U)
          (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).inv)).natTrans

/-- Invertibility of the proper finite coefficient comparison on every object.
The finite-free hypothesis supplies the coefficient basis used in the argument.
Source: Stacks Tags 0B56, 07A6, 0GL5 and 0GL6.
(blueprint: lem-pur-compact-support-finite-proper-comparison-iso).
Proof: the independent finite-free restriction/direct-image mate theorem proves
invertibility of the displayed mate after converting the supplied product basis
into a finite coproduct. The definition below is that same mate expression.
Rank zero and arbitrary derived inputs are included. -/
theorem finiteProperComparison_isIso {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) (d : ℕ)
    (hfree : Nonempty
      ((pbcRestrict (a.map V)).obj
          (SheafOfModules.unit ((adicLisseForget V).obj (S.ring V))) ≅
        ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget V).obj (R.ring V))))
    (K : DerivedCategory (pbcModules U (R.ring U))) :
    IsIso ((finiteProperComparison a g).app K) := by
  letI : IsIso (finiteProperComparison a g) := by
    simpa only [finiteProperComparison] using
      finiteFreeRestrictionDirectImageMate_isIso a g d hfree
  infer_instance

end WeilConjectures.PurCompactSupport
