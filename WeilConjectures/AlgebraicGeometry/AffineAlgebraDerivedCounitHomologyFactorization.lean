/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing


public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.AlgebraicGeometry.AffineDerivedCohomology
import WeilConjectures.AlgebraicGeometry.QCohAcyclicDerivedPushforwardCohomology
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleAdjunctionIsos
import WeilConjectures.AlgebraicGeometry.AffineAlgebraExactDerivedCounitIso
import WeilConjectures.AlgebraicGeometry.AffineAlgebraDerivedUnitHomologyFactorization
import WeilConjectures.AlgebraicGeometry.AffineAlgebraDerivedAdjunctionQCoh

/-! # Cohomology of the affine algebra derived counit

## References

* Stacks Project, Tag 0AVW
-/

@[expose] public section

universe v wX wA

open CategoryTheory

namespace AlgebraicGeometry

/-- Under the cohomology comparison, the derived affine algebra counit is the
underived counit applied to the cohomology module (Stacks, Tag 0AVW). -/
theorem affine_algebra_derived_counit_homology_factorization
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    [Limits.PreservesFiniteLimits P]
    (L : DerivedCategory (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) ⥤
      schemeDerivedCategory X)
    (adj : L ⊣ RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f))
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K) (n : ℤ) :
    ∃ e : (DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n).obj
          (L.obj ((RingedSpace.derivedModuleDirectImage
            (toDirectImageAlgebraSpace f)).obj K)) ≅
        P.obj ((RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n).obj K)),
      (DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n).map
          (adj.counit.app K) =
        e.hom ≫ a.counit.app ((DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n).obj K) := by
  let : P.Additive := a.left_adjoint_additive
  let : P.IsLeftAdjoint := a.isLeftAdjoint
  let adjD := a.mapDerivedCategoryRightDerivedAdjunction
  have : IsIso (adjD.counit.app K) :=
    affine_algebra_exact_derived_counit_isIso f P a K hK
  -- Transport the canonical exact-derived counit along uniqueness of left adjoints.
  have : IsIso (adj.counit.app K) := by
    rw [← adj.leftAdjointUniq_hom_app_counit adjD K]
    infer_instance
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n
  have : IsIso (a.counit.app (H.obj K)) :=
    (affine_algebra_module_adjunction_isos f P a).2.2 _ (hK n)
  -- The statement asks for some source comparison, so compose the two counits.
  let c := H.map (adj.counit.app K)
  refine ⟨asIso c ≪≫ (asIso (a.counit.app (H.obj K))).symm, ?_⟩
  change c = (c ≫ inv (a.counit.app (H.obj K))) ≫ a.counit.app (H.obj K)
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry
