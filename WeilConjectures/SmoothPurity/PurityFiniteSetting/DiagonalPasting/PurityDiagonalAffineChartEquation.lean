/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPastingData
import WeilConjectures.AlgebraicGeometry.DifferenceCoordinateSection.DifferenceFirstInputRestriction
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionBaseComparisonLaws
import WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

/-! # The affine chart equation of diagonal section pasting

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
  HomologicalComplex.monoidalCategory
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale.DifferenceCoordinateSection
open AlgebraicGeometry.ProEtale.FiniteEtaleNormalization hiding beta sigma

namespace WeilConjectures.PurityFiniteSetting.DiagonalPasting

private theorem bifunctor_postcomp_congr {C : Type*} [Category C]
    (T : C ⥤ C ⥤ C) {K K' M M' N : C}
    {a a' : K ⟶ K'} {b b' : M ⟶ M'} (ha : a = a') (hb : b = b')
    (c : (T.obj K').obj M' ⟶ N) :
    ((T.map a).app M ≫ (T.obj K').map b) ≫ c =
      ((T.map a').app M ≫ (T.obj K').map b') ≫ c := by
  cases ha
  cases hb
  rfl

set_option maxHeartbeats 2000000 in
-- The chart has many canonical compactifications and derived-comparison instances.
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory in
end WeilConjectures.PurityFiniteSetting.DiagonalPasting
