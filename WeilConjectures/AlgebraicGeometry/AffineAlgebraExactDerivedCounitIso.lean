/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.AffineAlgebraKInjectiveCounitHomologyFactorization
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleAdjunctionCounitIso
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # The canonical exact-derived affine algebra counit

## References

* Stacks Project, Tag 0AVW
-/

@[expose] public section

universe v wX wA

open CategoryTheory

namespace AlgebraicGeometry

/-- The counit of the canonical derived adjunction of an exact affine algebra pullback
is invertible on complexes with quasi-coherent cohomology (Stacks, Tags 0AVW and 079W). -/
theorem affine_algebra_exact_derived_counit_isIso
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    [P.Additive] [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P]
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K) :
    IsIso ((a.mapDerivedCategoryRightDerivedAdjunction).counit.app K) := by
  let C := SheafOfModules.{v} (moduleRings X.toRingedSpace)
  let R := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  have : I.IsKInjective := hI
  have hIQ : ∀ n : ℤ, (I.homology n).IsQuasicoherent := by
    intro n
    let c := (DerivedCategory.homologyFunctor C n).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors C n).app I
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      c (hK n)
  have hq : QuasiIso ((a.mapHomologicalComplex (.up ℤ)).counit.app I) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    obtain ⟨c, hc⟩ := affine_algebra_kinjective_counit_homology_factorization f P a I hIQ n
    have : R.IsRightAdjoint := a.isRightAdjoint
    let b := Adjunction.ofIsRightAdjoint R
    have : IsIso (b.counit.app (I.homology n)) :=
      affine_algebra_module_adjunction_counit_iso f _ (hIQ n)
    have : IsIso (a.counit.app (I.homology n)) := by
      rw [← a.leftAdjointUniq_hom_app_counit b (I.homology n)]
      infer_instance
    rw [hc]
    infer_instance
  let J := (HomotopyCategory.quotient C (.up ℤ)).obj I
  have hε := (a.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ))
    P.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit J
  have hQ : IsIso (DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).counit.app J)) := by
    dsimp [J]
    rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
    have : IsIso (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app I)) :=
      inferInstance
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C)
      ((a.mapHomologicalComplex (.up ℤ)).counit.app I)).mp this
  have hderived : IsIso (a.mapDerivedCategoryRightDerivedAdjunction.counit.app
      (DerivedCategory.Qh.obj J)) := by
    have : IsIso (P.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app J)) := by
      dsimp [J]
      infer_instance
    exact IsIso.of_isIso_fac_left hε
  have : IsIso (a.mapDerivedCategoryRightDerivedAdjunction.counit.app
      ((HomotopyCategory.quotient C (.up ℤ) ⋙ DerivedCategory.Qh).obj I)) := hderived
  let c := e ≪≫ ((DerivedCategory.quotientCompQhIso C).app I).symm
  have he := a.mapDerivedCategoryRightDerivedAdjunction.counit.naturality c.hom
  exact IsIso.of_isIso_fac_right he.symm

end AlgebraicGeometry
