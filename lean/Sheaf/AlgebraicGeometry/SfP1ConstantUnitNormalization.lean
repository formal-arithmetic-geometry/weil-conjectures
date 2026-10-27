/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.SfP1IntegralTransportData

/-! # Normalization of the constant derived unit -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local implicit_reducible] ordinaryFiniteDegreeZero ordinaryFiniteSingleFunctor
attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace
attribute [local instance 2000] Abelian.toPreadditive

/-- The extra constant-sheaf unit factor is the identity.

Source: the constructed constantUnit and the monoidal constant-sheaf functor.
(blueprint: lem-sf-p1-constant-unit-normalization)

Proof: the unit map of the constant-sheaf functor is the sheafification of the
identity of the constant coefficient unit, so it is the identity. Its inverse
is the identity by cancellation. Applying degree zero preserves the identity;
the remaining factor is exactly singleFunctorObjUnitIso. -/
theorem constantUnit_eq_single (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) :
    constantUnit A S = singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S := by
  have hε : (Functor.Monoidal.εIso
      (constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))).hom = 𝟙 _ := by
    change 𝟙 _ ≫ (presheafToSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).map
      (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have hε' : (Functor.Monoidal.εIso
      (constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))).inv = 𝟙 _ := by
    apply (cancel_epi (Functor.Monoidal.εIso
      (constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))).hom).mp
    rw [Iso.hom_inv_id, Category.comp_id, hε]
  unfold constantUnit
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    hε']
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

end AlgebraicGeometry.Etale.SfP1Transport
