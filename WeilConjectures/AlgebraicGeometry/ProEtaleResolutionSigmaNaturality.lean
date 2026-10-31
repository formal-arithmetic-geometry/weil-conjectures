/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackDescentData

/-! # Naturality of the specified inverse total-tensor comparison at (1,q).

(blueprint: lem-sp-resolution-sigma-naturality)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] proEtaleTensorPullbackTotal proEtaleTensorPullbackTotalIso
  proEtaleRingDerivedPullbackFactors CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf
  HomologicalComplex₂.total
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- Naturality of the specified inverse total-tensor comparison at (1,q).
Source: Stacks Project, Cohomology on Sites, Tags 06YP, 06YS, 06YU and 07A4.
(blueprint: lem-sp-resolution-sigma-naturality). -/
theorem proEtale_resolution_sigma_naturality
    (P H M : CochainComplex (proEtaleRingModules Y R) ℤ) (q : H ⟶ M) :
    ((proEtaleTensorPullbackTotalIso f R S c P H).symm).hom ≫
        ((Functor.uncurry.obj ((proEtaleOrdinaryTensor X S).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))).map (Prod.mkHom
          (𝟙 ((((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))).obj P))
          ((((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))).map q))) =
      (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))).map
          (((Functor.uncurry.obj ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))).map (Prod.mkHom (𝟙 P) q))) ≫
        ((proEtaleTensorPullbackTotalIso f R S c P M).symm).hom := by
  obtain ⟨_, _, σ, hσ⟩ := proEtaleTensorPullbackDescentData f R S c
  have hn := σ.inv.naturality (X := (P, H)) (Y := (P, M)) (Prod.mkHom (𝟙 P) q)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [(((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))).map_id P, hσ P H, hσ
      P M] at hn
  exact hn.symm


end AlgebraicGeometry.Scheme
