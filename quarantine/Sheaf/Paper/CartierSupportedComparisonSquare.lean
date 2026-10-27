/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.Paper.ComparisonImageClosedSectionNormalization

/-! # Exact-single comparison of the supported Cartier arrow

Source: current blueprint rank-one Thom proof, Step 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w c
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.PurityFiniteSetting
set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupSheaves functorialCupCategory functorialCupAbelian
  functorialCupHasDerived functorialCupSingle functorialCupComparisonFunctor

variable (P : PurityFiniteSetting.{u})

/-- Canonical degree-zero Cartier comparison endpoint.
Source: rank-one Thom Step 1
(blueprint: lem-pur-cartier-supported-comparison-square). -/
def cartierComparisonEtaleTarget (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
  ⟨((DerivedCategory.singleFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj
      (P.frameTwistEtale T 1))⟦(2 : ℤ)⟧,
    DerivedCategory.TStructure.t.plus.le_shift (2 : ℤ) _
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj
        (P.frameTwistEtale T 1)).property⟩

/-- Canonical degree-zero Cartier comparison endpoint.
Source: rank-one Thom Step 1
(blueprint: lem-pur-cartier-supported-comparison-square). -/
def cartierComparisonProTarget (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) :=
  ⟨((DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
      (P.functorialCupTwist true T 1))⟦(2 : ℤ)⟧,
    DerivedCategory.TStructure.t.plus.le_shift (2 : ℤ) _
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
        (P.functorialCupTwist true T 1)).property⟩

/-- Canonical degree-zero Cartier comparison endpoint.
Source: rank-one Thom Step 1
(blueprint: lem-pur-cartier-supported-comparison-square). -/
def cartierComparisonTwist (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
      (P.cartierComparisonEtaleTarget T).obj ≅ (P.cartierComparisonProTarget T).obj :=
  ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.commShiftIso
    (2 : ℤ)).app
    ((DerivedCategory.singleFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj
      (P.frameTwistEtale T 1)) ≪≫
  (shiftFunctor _ (2 : ℤ)).mapIso
    (((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategorySingleFunctor
      0).app
      (P.frameTwistEtale T 1))

/-- The canonical bounded-below etale Cartier arrow.
Source: rank-one Thom Step 1
(blueprint: lem-pur-cartier-supported-comparison-square). -/
def cartierComparisonEtaleMap {D T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k))
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    closedSectionSe P i ⟶ P.cartierComparisonEtaleTarget T :=
  ObjectProperty.homMk (P.agreementCartierEtale a i hI).hom

/-- The canonical bounded-below pro-etale Cartier arrow.
Source: rank-one Thom Step 1
(blueprint: lem-pur-cartier-supported-comparison-square). -/
def cartierComparisonProMap {D T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k))
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    closedSectionSp P i ⟶ P.cartierComparisonProTarget T :=
  ObjectProperty.homMk (P.agreementCartierMap a i hI)

/-- The supported Cartier arrow commutes with exact-single site comparison.

Source: current blueprint, sec-smooth-purity/sk-prop-an,
thm-pur-rank-one-thom.proof.md, Step 1; supported etale realization square.
(blueprint: lem-pur-cartier-supported-comparison-square).

Proof: expand agreementCartierMap and functorialCupCompare. The latter begins
with the single image of the inverse supported-source comparison. The hom of
closedSectionEpsilon contributes the single image of that comparison, so these
factors cancel by functoriality and the isomorphism inverse law. The exact-single
comparison and its inverse cancel next. The remaining factors are the derived
image of the etale class, the shift comparison, and the shifted single comparison.
The target equality transport is the identity, since functorialCupTwist true is
the comparison image of the same finiteEtaleTateSheaf. The argument uses no
geometric property beyond closedness, and works for the zero class, empty
support and ramified coefficient levels. It does not assert that the Cartier
arrow is invertible. -/
theorem cartierSupported_comparison_square (P : PurityFiniteSetting.{u})
    {D T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k))
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map
        (P.cartierComparisonEtaleMap a i hI).hom ≫ (P.cartierComparisonTwist T).hom =
      (closedSectionEpsilon P i).hom ≫ (P.cartierComparisonProMap a i hI).hom := by
  sorry

end WeilConjectures.PurityFiniteSetting
