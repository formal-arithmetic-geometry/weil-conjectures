/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import WeilConjectures.WeilSheaf.SmoothPurity
import WeilConjectures.WeilSheaf.SmoothPurityEquivariantIsoLift
import WeilConjectures.WeilSheaf.SmoothPurityCanonicalLift
import WeilConjectures.WeilSheaf.SmoothPurityCanonicalUnique
import WeilConjectures.WeilSheaf.SmoothPurityTraceNormalization
import WeilConjectures.WeilSheaf.SmoothPurityFiniteEquivariance

/-! # Dependency audit of the orientation reconstruction helpers

The assigned Weil leaf is not asserted to be closed by this audit.
-/

#print axioms AlgebraicGeometry.ProEtale.CondensedRing.eq_of_isIntegralSmoothOrientation
#print axioms AlgebraicGeometry.ProEtale.CondensedRing.exists_isIntegralSmoothOrientation_of_compatible
#print axioms AlgebraicGeometry.ProEtale.CondensedRing.isIntegralSmoothOrientation_iff_trace
#print axioms AlgebraicGeometry.ProEtale.CondensedRing.exists_equivariant_iso_of_finite_reductions
#print axioms AlgebraicGeometry.Etale.isWeilMorphism_dualizingComplexTwistShiftIso_inv
