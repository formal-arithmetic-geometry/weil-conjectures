/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomScalarTensorNormalization
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarMonoidal

/-! # Scalar tensor comparison and inverse Koszul symmetry
Source: blueprint thm-coef-finite-hom, evaluation paragraph
(blueprint: lem-coef-finite-hom-scalar-tensor-braid).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b c d w z
open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard

-- Use the coefficient and sheaf braidings fixed in the ordinary derived tensor.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000]
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall

attribute [local implicit_reducible] CategoryTheory.uniformProd
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory Etale.sheafMonoidalClosed
  ModuleCat.MonoidalCategory.instBraidedCategory

attribute [local implicit_reducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local implicit_reducible]
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution

attribute [local irreducible] DerivedCategory.monoidalClosed

private theorem inverseSquare {C : Type a} [Category.{b} C]
    {D : Type c} [Category.{d} D] (F : C ⥤ D) {P Q : C} {U V : D}
    (e : P ≅ Q) (e' : U ≅ V) (t : U ⟶ F.obj P) (s : V ⟶ F.obj Q)
    (h : e'.hom ≫ s = t ≫ F.map e.hom) :
    e'.inv ≫ t = s ≫ F.map e.inv := by
  apply (cancel_epi e'.hom).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, h, Category.assoc, ← F.map_comp]
  rw [Iso.hom_inv_id, F.map_id, Category.comp_id]

set_option maxHeartbeats 1600000 in
-- The derived-instance conversions require additional kernel heartbeats.
end WeilConjectures
