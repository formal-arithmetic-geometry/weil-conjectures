/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleExternalKunneth
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-! # A constructed factor-interchange comparison for external products

Source: sk-lem-sf-kunneth-star, Two morphisms, exchanging the factors
(blueprint: lem-sf-external-kunneth-swap).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale

/-- Exchange the factors by the unit of the pullback/direct-image equivalence, the
pullback tensor comparison, the two projection identities, and tensor symmetry.
No object or map is chosen from an existence theorem.
Source: sk-lem-sf-kunneth-star, Two morphisms
(blueprint: lem-sf-external-kunneth-swap). -/
def externalKunnethSwapIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B X Y : Scheme.{u}} (b : X ⟶ B) (c : Y ⟶ B)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (Q : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) :
    externalProduct (ModuleCat.{u + 1} A) b c M Q ≅
      (lowerStar (ModuleCat.{u + 1} A) (pullbackSymmetry b c).inv).rightDerivedFunctor.obj
        (externalProduct (ModuleCat.{u + 1} A) c b Q M) := by
  letI := _root_.DerivedCategory.braidedCategory'
    (Sheaf (Scheme.ProEt.topology (pullback c b)) (ModuleCat.{u + 1} A))
  let s := (pullbackSymmetry b c).inv
  let F := (upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor
  let G := (lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor
  let P := externalProduct (ModuleCat.{u + 1} A) b c M Q
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s
  have : IsIso s := inferInstance
  have : F.IsEquivalence := inferInstance
  let e₁ := ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s
      (pullback.fst b c)).symm.app M) ≪≫
    ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} A)
      (pullbackSymmetry_inv_comp_fst b c)).app M)
  let e₂ := ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s
      (pullback.snd b c)).symm.app Q) ≪≫
    ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} A)
      (pullbackSymmetry_inv_comp_snd b c)).app Q)
  let e := leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) s _ _ ≪≫
    tensorIso e₁ e₂ ≪≫ β_ _ _
  exact asIso (adj.unit.app P) ≪≫ G.mapIso e

end AlgebraicGeometry.ProEtale
