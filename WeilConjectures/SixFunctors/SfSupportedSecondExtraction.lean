/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfSupportedDiagonalDataSupplement
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence

/-! # Second coordinate extraction before a trace

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, second triangle, common coefficient extraction.
(blueprint: lem-sf-supported-second-extraction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
open MonoidalCategory BraidedCategory

open MonoidalCategory BraidedCategory in
open MonoidalCategory BraidedCategory in
open MonoidalCategory BraidedCategory in
private theorem inverse_square
    {D : Type*} [Category D] {H X Y Z W : D}
    (a : H ≅ X) (d : X ≅ Y) (q : Z ≅ Y) (t : W ≅ Z) (δ : H ≅ W)
    (h : a.hom ≫ d.hom = δ.hom ≫ t.hom ≫ q.hom) :
    a.inv = d.hom ≫ q.inv ≫ t.inv ≫ δ.inv := by
  apply (cancel_epi a.hom).1
  rw [reassoc_of% h]
  simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id]

namespace AlgebraicGeometry.Etale.SupportedTrace

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  _root_.DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions

section GeneralCoefficients

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [UpperStarPreservesFlat C]

end GeneralCoefficients

variable (A : Type (u + 1)) [CommRing A] [Finite A]

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

open MonoidalCategory BraidedCategory in
attribute [local irreducible] projectionIso projectionRightIso
  TraceDiagonalDatum.baseChangeIso

end AlgebraicGeometry.Etale.SupportedTrace
