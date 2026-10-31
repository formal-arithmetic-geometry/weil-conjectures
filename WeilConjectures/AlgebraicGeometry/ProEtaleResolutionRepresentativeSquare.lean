/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # The specified canonical comparison on two flat representatives.

(blueprint: lem-sp-resolution-representative-square)
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

/-- The specified canonical comparison on two flat representatives.
Source: Stacks Project, Cohomology on Sites, Tags 06YP, 06YS, 06YU and 07A4.
(blueprint: lem-sp-resolution-representative-square). -/
theorem proEtale_resolution_representative_square
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
    (P H : CochainComplex (proEtaleRingModules Y R) ℤ)
    (hP : proEtaleFlatRepresentatives Y R P)
    (hH : proEtaleFlatRepresentatives Y R H)
    (hFP : proEtaleFlatRepresentatives X S ((((proEtaleRingModulePullback f R S
        c).mapHomologicalComplex (.up ℤ))).obj P))
    (hFH : proEtaleFlatRepresentatives X S ((((proEtaleRingModulePullback f R S
        c).mapHomologicalComplex (.up ℤ))).obj H)) :
    (proEtaleRingDerivedPullback f R S c).map
        (a.representative.hom.app (⟨P, hP⟩, ⟨H, hH⟩)) ≫
      (proEtaleCanonicalTensorComparison f R S c a b).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj H) ≫
      b.tensor.map (Prod.mkHom
        ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P)
        ((proEtaleRingDerivedPullbackFactors f R S c).hom.app H)) =
    (proEtaleRingDerivedPullbackFactors f R S c).hom.app
        (((Functor.uncurry.obj ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)))).obj (P, H)) ≫
      DerivedCategory.Q.map ((proEtaleTensorPullbackTotalIso f R S c P H).symm).hom ≫
        b.representative.hom.app
          (⟨(((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))).obj P, hFP⟩,
            ⟨(((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))).obj H, hFH⟩)
                := by
  obtain ⟨_, _, hh⟩ := (Classical.choose_spec
    (proEtaleCanonicalTensorPullback f R S c a b).2.exists) P H hP hH
  exact hh


end AlgebraicGeometry.Scheme
