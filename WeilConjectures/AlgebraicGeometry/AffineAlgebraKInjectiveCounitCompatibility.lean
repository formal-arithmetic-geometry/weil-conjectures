/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry

/-- The canonical homology comparison obtained as the adjoint mate of the homology
of the termwise counit, after the exact left-adjoint comparison. This is a real
construction, independent of any existence theorem for a cohomology isomorphism (Stacks, Tag 0AVW).
-/
noncomputable def affineAlgebraCounitHomologyComparison
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    [P.Additive] [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P]
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    (n : ℤ) :
    (((RingedSpace.moduleDirectImage
      (toDirectImageAlgebraSpace f)).mapHomologicalComplex (.up ℤ)).obj I).homology n ⟶
      (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).obj (I.homology n) :=
  a.homEquiv _ _
    ((P.mapHomologicalComplexHomologyIso (.up ℤ) n).inv.app
      (((RingedSpace.moduleDirectImage
        (toDirectImageAlgebraSpace f)).mapHomologicalComplex (.up ℤ)).obj I) ≫
      HomologicalComplex.homologyMap ((a.mapHomologicalComplex (.up ℤ)).counit.app I) n)

/-- The homology of the termwise counit factors through its canonical adjoint mate
(Stacks, Tag 0AVW). -/
theorem affine_algebra_kinjective_counit_compatibility
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    [P.Additive] [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P]
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    (n : ℤ) :
    HomologicalComplex.homologyMap ((a.mapHomologicalComplex (.up ℤ)).counit.app I) n =
      (P.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app
        (((RingedSpace.moduleDirectImage
          (toDirectImageAlgebraSpace f)).mapHomologicalComplex (.up ℤ)).obj I) ≫
        P.map (affineAlgebraCounitHomologyComparison f P a I n) ≫
          a.counit.app (I.homology n) := by
  let c := (P.mapHomologicalComplexHomologyIso (.up ℤ) n).app
    (((RingedSpace.moduleDirectImage
      (toDirectImageAlgebraSpace f)).mapHomologicalComplex (.up ℤ)).obj I)
  have h := (a.homEquiv _ _).symm_apply_apply
    (c.inv ≫ HomologicalComplex.homologyMap
      ((a.mapHomologicalComplex (.up ℤ)).counit.app I) n)
  rw [Adjunction.homEquiv_symm_apply] at h
  change _ = c.hom ≫ _ ≫ _
  unfold affineAlgebraCounitHomologyComparison
  erw [h, c.hom_inv_id_assoc]

end AlgebraicGeometry
