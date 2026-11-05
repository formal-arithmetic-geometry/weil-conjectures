/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Statement
public import WeilConjectures.WeilSheaf.SmoothPurity
public import WeilConjectures.LeanEval.WeilConjectures

/-! # Axiom audit for the Weil conjectures statement

Declaration-level closure check (C9, 2026-11-06): the lean-eval statement must not depend on
`sorryAx`; in particular not on
`AlgebraicGeometry.WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso`
(SmoothPurity.lean), whose two former consumers (`nonempty_dualizingComplex_iso`, Y = Spec k₀, and
the affine-line Thom user in `FourierInversion.OtherSections`) are routed through absolute purity. -/

#print axioms AlgebraicGeometry.Scheme.weil_conjectures
#print axioms LeanEval.AlgebraicGeometry.WeilConjectures.weil_conjectures
#print axioms AlgebraicGeometry.WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso
