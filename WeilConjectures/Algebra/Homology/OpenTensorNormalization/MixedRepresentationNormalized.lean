/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.AlgebraicGeometry.FiniteOpenMixedTensorRepresentative

/-! Mixed localization representative normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace SheafOfModules.OpenTensorNormalization

set_option maxHeartbeats 2000000 in
-- Normalize only the published mixed comparison components.
/-- Normalizes the published mixed tensor representative equation to the finite model
aliases used by the restriction square. Source: Stacks Tag 07A4, clause (3) of
`finiteOpenMixedTensorRepresentative`. The proof expands the finite total and the
canonical map-derived tensor comparison, transports the inverse of the oplax map by
`Functor.map_inv`, and identifies the derived tensor map with tensoring by the identity.
(blueprint: lem-sf-mixed-representation-normalized) -/
theorem mixed_representation_normalized
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P Q : CochainComplex (ProEtale.FiniteCoeffSheaf (A := A) X) ℤ) :
    let F := ProEtale.FiniteCoeffUpperStar (A := A) j
    let a := F.mapDerivedCategoryFactors.hom
    let muX := Functor.LaxMonoidal.μ
      (DerivedCategory.Q (C := ProEtale.FiniteCoeffSheaf (A := A) X)) P Q
    let fc := F.mapHomologicalComplex (.up ℤ)
    let muU := Functor.LaxMonoidal.μ (DerivedCategory.Q (C := ProEtale.FiniteCoeffSheaf (A := A) U))
      (fc.obj P) (fc.obj Q)
    let c := ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q
    let delta := ((ProEtale.mapDerivedCategoryUpperStarDerivedTensorIso
      (ModuleCat.{u + 1} A) j).hom.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q)
    let n := a.app P ⊗ₘ (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app
      (DerivedCategory.Q.obj Q) ≫ a.app Q)
    delta ≫ F.mapDerivedCategory.map muX ≫ a.app (HomologicalComplex.mapBifunctor P Q
      (ProEtale.FiniteCoeffCoTensor (A := A) X) (.up ℤ)) =
      n ≫ muU ≫ DerivedCategory.Q.map (inv c) := by
  dsimp only
  let F := ProEtale.FiniteCoeffUpperStar (A := A) j
  let a := F.mapDerivedCategoryFactors.hom
  let muX := Functor.LaxMonoidal.μ
    (DerivedCategory.Q (C := ProEtale.FiniteCoeffSheaf (A := A) X)) P Q
  let fc := F.mapHomologicalComplex (.up ℤ)
  let muU := Functor.LaxMonoidal.μ (DerivedCategory.Q (C := ProEtale.FiniteCoeffSheaf (A := A) U))
    (fc.obj P) (fc.obj Q)
  let c := ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q
  let delta := ((ProEtale.mapDerivedCategoryUpperStarDerivedTensorIso
    (ModuleCat.{u + 1} A) j).hom.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q)
  let n := a.app P ⊗ₘ (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app
    (DerivedCategory.Q.obj Q) ≫ a.app Q)
  have hdelta : delta =
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) U).map
        ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) j).inv.app (DerivedCategory.Q.obj P))).app
          (F.leftDerivedFunctor.obj (DerivedCategory.Q.obj Q)) ≫
      ((ProEtale.leftDerivedUpperStarTensorNatIso
        (ModuleCat.{u + 1} A) j).inv.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q) ≫
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) j).hom.app
        (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
          (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj Q)) := by
    rfl
  have hdelta' : delta =
      (F.leftDerivedFunctorIsoMapDerivedCategory.inv.app (DerivedCategory.Q.obj P) ⊗ₘ
        𝟙 (F.leftDerivedFunctor.obj (DerivedCategory.Q.obj Q))) ≫
      ((ProEtale.leftDerivedUpperStarTensorNatIso
        (ModuleCat.{u + 1} A) j).inv.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q) ≫
      F.leftDerivedFunctorIsoMapDerivedCategory.hom.app
        (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) := by
    rw [hdelta]
    simp only [ProEtale.leftDerivedUpperStarIsoMapDerivedCategory,
      ProEtale.derivedTensor, curriedTensor_map_app, tensorHom_id]
    rfl
  change delta ≫ F.mapDerivedCategory.map muX ≫ a.app (HomologicalComplex.mapBifunctor P Q
      (ProEtale.FiniteCoeffCoTensor (A := A) X) (.up ℤ)) =
    n ≫ muU ≫ DerivedCategory.Q.map (inv c)
  rw [hdelta', Functor.map_inv]
  simp only [Category.assoc]
  exact (ProEtale.finiteOpenMixedTensorRepresentative (A := A) j P Q).2.2

end SheafOfModules.OpenTensorNormalization
