/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineAlgebraUpperTruncationEdge
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-! # Exactness of affine cycles and boundaries

Source: Stacks Project, Tags 0AVW and 08D4.
-/

@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- After affine direct image, cycle sections with zero homology class are
locally boundaries of the section complex.
Source: Stacks Project, Tag 0AVW, the cohomology calculation in its proof;
Tag 08D4, parts (1) and (2), with bound one. -/
theorem affine_algebra_kinjective_boundary_exactness
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ) :
    ((ShortComplex.mk (I.sc n).homologyData.left.f' (I.sc n).homologyData.left.π
      (I.sc n).homologyData.left.f'_π).map
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))).Exact := by
  let C := SheafOfModules.{v} (moduleRings X.toRingedSpace)
  let D := SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  have : EnoughInjectives C :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let h := (I.sc n).homologyData.left
  have : IsIso ((DerivedCategory.homologyFunctor D n).map
      (F.complexDerivedUnit.app (I.truncLE n))) :=
    F.isIso_complexDerivedUnit_upperTruncation I n
  have : IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map (I.ιTruncLE n)) n) :=
    (F.upperTruncation_comparisons I n).1
  have : IsIso (F.upperTruncationBoundaryComparison I n) := by
    dsimp [Functor.upperTruncationBoundaryComparison]
    infer_instance
  obtain ⟨e, he⟩ := affine_algebra_upper_truncation_edge f I hI n
  let B := (ShortComplex.mk h.f' h.π h.f'_π).map F
  apply B.exact_iff_mono_cokernel_desc.mpr
  have hd : Limits.cokernel.desc B.f B.g B.zero =
      F.upperTruncationBoundaryComparison I n ≫ e.hom := by
    apply (cancel_epi (Limits.cokernel.π B.f)).mp
    rw [Limits.cokernel.π_desc]
    dsimp only [B, ShortComplex.map, ShortComplex.mk, h, F]
    exact he.symm
  rw [hd]
  infer_instance

end AlgebraicGeometry
