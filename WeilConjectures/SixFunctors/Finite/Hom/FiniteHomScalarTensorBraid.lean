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

private theorem inverseSquare_congr {C : Type a} [Category.{b} C]
    {D : Type c} [Category.{d} D] (F : C ⥤ D) {P Q : C} {U V : D}
    (e : P ≅ Q) (e' : U ≅ V) (t : U ⟶ F.obj P) (s : V ⟶ F.obj Q)
    (t' : U ⟶ F.obj P) (s' : V ⟶ F.obj Q) (ht : t = t') (hs : s = s')
    (h : e'.hom ≫ s = t ≫ F.map e.hom) :
    e'.inv ≫ t' = s' ≫ F.map e.inv := by
  cases ht
  cases hs
  exact inverseSquare F e e' t s h

/-- The ordinary scalar tensor comparison respects inverse Koszul symmetry.
Source: blueprint thm-coef-finite-hom, opening evaluation paragraph.
(blueprint: lem-coef-finite-hom-scalar-tensor-braid).

Proof: choose the existing normalized core monoidal scalar structure. Tensor
normalization identifies its tensorator with the ordinary scalar comparison.
Its braid square implies the inverse braid square by cancelling the target
braiding and applying functoriality to the source inverse. This works for every
pair of objects, including zero objects and identity coefficient maps. -/
theorem finiteHom_scalar_tensor_braid {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (K L : Etale.DerivedCategoryModule A X) :
    (finiteHomKoszulIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
        ((Etale.scalarExtension φ X).obj K) ((Etale.scalarExtension φ X).obj L)).inv ≫
      (Etale.etaleHomTensorComparison X φ K L).hom =
    (Etale.etaleHomTensorComparison X φ L K).hom ≫ (Etale.scalarExtension φ X).map
      (finiteHomKoszulIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) K L).inv := by
  obtain ⟨c, _, hc, hb⟩ := Etale.ExceptionalCoefficients.scalarExtension_coreMonoidal
    A B φ X
  have he (P Q) : (c.μIso P Q).hom = (Etale.etaleHomTensorComparison X φ P Q).hom := by
    exact (congrArg Iso.inv (hc P Q)).trans (finiteHom_scalar_tensor_normalization φ X P Q)
  exact inverseSquare_congr (Etale.scalarExtension φ X) _ _
    (c.μIso K L).hom (c.μIso L K).hom _ _ (he K L) (he L K) (hb K L)

set_option maxHeartbeats 1600000 in
-- The derived-instance conversions require additional kernel heartbeats.
end WeilConjectures
