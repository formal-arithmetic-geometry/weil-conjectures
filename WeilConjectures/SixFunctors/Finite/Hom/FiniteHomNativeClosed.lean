/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow

/-! The native derived closed record with its internal Hom fixed before specialization. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b w
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.uniformProd
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory Etale.sheafMonoidalClosed

attribute [local irreducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution
  DerivedCategory.monoidalClosed

/-- The native right-tensor closed record, with its internal Hom fixed abstractly.
Source: blueprint thm-coef-finite-hom, opening evaluation paragraph.
(blueprint: def-coef-finite-hom-native-closed).

Construction: use the uniquely normalized Koszul braiding on the derived category,
then take finiteHomClosed. Its monoidal structure, right-tensor adjunction and
naturality proof are actual existing data; no existence witness supplies new data.
The internal Hom is shared before any coefficient category is specialized. -/
def finiteHomNativeDerivedClosed
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] :
    CoefficientClosedStructure (finiteHomDerivedInternalHomGeneral C) :=
  letI := finiteHomDerivedBraiding C
  finiteHomClosed

end WeilConjectures
