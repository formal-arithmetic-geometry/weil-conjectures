/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ClosedImmersionAlgebraDirectImageExact
import WeilConjectures.AlgebraicGeometry.ClopenRankStrataFormality
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Reconstruction from cohomology on finitely many rank strata

## References

* Stacks Project, Tags 0BQZ and 0AVW
-/

@[expose] public section

universe u wZ wA

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Over the algebra of a closed immersion, rank-stratified cohomology determines
its derived object. (Stacks, Tags 0BQZ, 0AVW) -/
theorem closedImmersion_rankedCohomology_reconstruction
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i)))]
    (M : Z.Modules) (r : LocallyConstant Z ℕ) (hfinite : (Set.range r).Finite)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))
    (hK : ∀ n : ℤ, Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj K ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj
          (Scheme.Modules.locallyRankedExteriorTerm M r n))) :
    Nonempty ((RingedSpace.derivedModuleDirectImage
      (toDirectImageAlgebraSpace i)).obj (DerivedCategory.Q.obj
        (Scheme.Modules.locallyRankedExteriorComplex M r)) ≅ K) := by
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)
  let : PreservesFiniteLimits F := by
    unfold F RingedSpace.moduleDirectImage
    infer_instance
  let : PreservesFiniteColimits F :=
    closedImmersion_algebraDirectImage_preservesFiniteColimits i
  let C := Scheme.Modules.locallyRankedExteriorComplex M r
  let e : (RingedSpace.derivedModuleDirectImage
      (toDirectImageAlgebraSpace i)).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
    F.rightDerivedFunctorIsoMapDerivedCategory.app (DerivedCategory.Q.obj C) ≪≫
      F.mapDerivedCategoryFactors.app C
  let E (n : ℕ) := Scheme.Modules.exteriorPower
    ((Scheme.Modules.restrictFunctor (Scheme.Modules.exteriorRankOpen r n).ι).obj M) n
  obtain ⟨eK⟩ := clopenRankStrata_formality i r hfinite E
    (Scheme.Modules.locallyRankedExteriorTerm M r) (fun _ => rfl) K hK
  exact ⟨e ≪≫ eK⟩

end AlgebraicGeometry
