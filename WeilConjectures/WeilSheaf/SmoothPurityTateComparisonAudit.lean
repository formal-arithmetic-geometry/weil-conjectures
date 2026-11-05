/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import WeilConjectures.WeilSheaf.SmoothPurityIntegralTateReductionPullback
import WeilConjectures.WeilSheaf.SmoothPurityIntegralTateRationalShift
import WeilConjectures.WeilSheaf.SmoothPurityRationalTrivializationScalar

/-! # Axiom audit for the actual Tate coefficient and pullback comparisons

This checks the Tate comparisons only; it does not assert that the Weil orientation
existence theorem has been proved.
-/

open AlgebraicGeometry.ProEtale

#print axioms upperStarIntegralTateTwistOneIso_hom_comp_reduction
#print axioms upperStarIntegralTateTwistNatIso_hom_comp_rationalization
#print axioms upperStarIntegralTateTwistDerivedIso_hom_comp_rationalization
#print axioms upperStarShiftIntegralTateTwistDerivedIso_hom_comp_rationalization
#print axioms CondensedRing.purity_commShift_derivedUpperStarExtendScalarsIso_hom

#print axioms purityRationalTateTrivialization_comp_specGeometricFrobenius_hom
