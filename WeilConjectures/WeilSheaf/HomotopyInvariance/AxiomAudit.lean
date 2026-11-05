/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.AffineLineBundle

/-!
# Axiom audit for affine-line homotopy invariance

The build log records the axioms used by the homotopy-invariance theorem, including any
remaining dependencies on the other Weil-complex leaves.
-/

#print axioms
  AlgebraicGeometry.ProEtale.CondensedRing.isIso_affineLineUnit_app_tensorUnit_padicAlgCl
#print axioms AlgebraicGeometry.WeilComplex.isIso_unit_app_toComplex_of_isLisse
#print axioms AlgebraicGeometry.WeilComplex.isIso_baseChange_of_smooth
#print axioms
  AlgebraicGeometry.WeilComplex.isIso_upperStarDerivedLowerStarAdjunction_unit_app_of_isPullback
