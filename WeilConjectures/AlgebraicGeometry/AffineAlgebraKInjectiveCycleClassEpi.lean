/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineOpenDerivedTruncationComparison
import WeilConjectures.AlgebraicGeometry.KInjectiveSectionCycleComparison
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! # Surjectivity of affine cycle classes

Source: Stacks Project, Tags 0AVW and 08D4.
-/

@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry

/-- Direct image of the cycle-class projection of an affine K-injective complex
with quasi-coherent cohomology is an epimorphism (Stacks, Tags 0AVW and 08D4). -/
theorem affine_algebra_kinjective_cycle_class_epi
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ) :
    Epi ((RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).map
      (I.sc n).homologyData.left.π) := by
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let p := F.map (I.sc n).homologyData.left.π
  have hsurj (U : X.Opens) (hU : IsAffineOpen U) :
      Function.Surjective ((I.sc n).homologyData.left.π.val.app (Opposite.op U)) := by
    let E := SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.evaluation (moduleRings X.toRingedSpace).obj (Opposite.op U)
    let := HasDerivedCategory.standard
      (SheafOfModules.{v} (moduleRings X.toRingedSpace))
    let := HasDerivedCategory.standard
      (ModuleCat.{v} ((moduleRings X.toRingedSpace).obj.obj (Opposite.op U)))
    have : EnoughInjectives
        (SheafOfModules.{v} (moduleRings X.toRingedSpace)) :=
      (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
    have hcomp := affine_open_derived_truncation_comparison X U hU I hI n
    have hiso := kInjective_section_cycle_comparison E I n hcomp
    let := hiso
    have hepi : Epi (E.map (I.sc n).homologyData.left.π) := by
      let h := (I.sc n).homologyData.left
      have hw : E.map h.f' ≫ E.map h.π = 0 := by
        rw [← E.map_comp, h.f'_π, E.map_zero]
      have hfac := CategoryTheory.Limits.cokernel.π_desc (E.map h.f') (E.map h.π) hw
      rw [← hfac]
      infer_instance
    exact (ModuleCat.epi_iff_surjective _).mp hepi
  have hlocal : TopCat.Presheaf.IsLocallySurjective
      ((PresheafOfModules.toPresheaf _).map p.val) := by
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro W y x hx
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hx
    have hs : Function.Surjective (p.val.app (Opposite.op V)) := by
      exact hsurj (f ⁻¹ᵁ V) (hV.preimage f)
    obtain ⟨z, hz⟩ := hs ((F.obj (I.sc n).homologyData.left.H).val.map
      (homOfLE hVW).op y)
    exact ⟨V, hVW, ⟨z, hz⟩, hxV⟩
  have : Sheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf (moduleRings (directImageAlgebraSpace f))).map p) := hlocal
  exact (SheafOfModules.toSheaf (moduleRings (directImageAlgebraSpace f))).epi_of_epi_map
    (Sheaf.epi_of_isLocallySurjective _)

end AlgebraicGeometry
