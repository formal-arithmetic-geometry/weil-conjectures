/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityAbsolute
public import WeilConjectures.WeilSheaf.SmoothPurityThomFromTate
public import WeilConjectures.WeilSheaf.VerdierDual
public import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
public import WeilConjectures.WeilSheaf.SmoothPurityTraceReductionTransport

/-! # Axiom audit for absolute purity and its trivial-line Thom consequence -/

#print axioms AlgebraicGeometry.WeilSheaf.purity_nonempty_toCondensedTateDescentIso
#print axioms AlgebraicGeometry.WeilComplex.purity_nonempty_shriekRightAdjoint_adicConstant_iso
#print axioms AlgebraicGeometry.WeilComplex.purity_nonempty_trivialLineThom
#print axioms AlgebraicGeometry.WeilComplex.nonempty_dualizingComplex_iso
#print axioms
  AlgebraicGeometry.WeilComplex.nonempty_iso_upperStar_comp_derivedLowerShriek_of_isPullback
#print axioms CategoryTheory.purity_isWeilEquivariant_reducedTrace
