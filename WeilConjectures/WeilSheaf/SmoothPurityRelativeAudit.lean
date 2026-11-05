/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurity
import Lean

/-! # Axiom audit of relative Weil orientation

The orientation and its relative base-change input must use only the standard axioms.
The final adjunction is also printed, including its separately assigned co-projection input.
-/

#print axioms AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothUnitBaseChange_descendedShriekGeometricExchange
#print axioms AlgebraicGeometry.WeilSheaf.purity_nonempty_toCondensedTateDescentIso
#print axioms AlgebraicGeometry.WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso
#print axioms AlgebraicGeometry.WeilComplex.nonempty_upperShriek_obj_adicConstant_iso_of_smooth
#print axioms AlgebraicGeometry.WeilComplex.exists_coprojection_forget_eq_upperShriekUnitTensorMap
#print axioms AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_adjunction_of_smooth

open Lean in
run_elab do
  for name in #[
      `AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothUnitBaseChange_descendedShriekGeometricExchange,
      `AlgebraicGeometry.WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso,
      `AlgebraicGeometry.WeilComplex.nonempty_upperShriek_obj_adicConstant_iso_of_smooth] do
    for axiomName in (← collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Relative purity {name} depends on unexpected axiom {axiomName}"
