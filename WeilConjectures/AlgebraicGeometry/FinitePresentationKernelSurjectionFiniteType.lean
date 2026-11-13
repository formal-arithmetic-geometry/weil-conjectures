/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalComparison
import WeilConjectures.AlgebraicGeometry.FinitePresentationKernelComparison

/-!
# Finite type of kernels of finite free surjections

## References

* Stacks Project, Tag 01BP
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- If a module has a local finite presentation, the kernel of a finite free
surjection onto it is locally of finite type. (Stacks, Tag 01BP) -/
theorem finitePresentation_kernel_surjection_finiteType
    (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X))
    [F.IsFinitePresentation]
    (r : ℕ)
    (ψ : SheafOfModules.free (R := moduleRings X) (ULift.{u} (Fin r)) ⟶ F)
    (hψ : Epi ψ) :
    (kernel ψ).IsFiniteType := by
  classical
  choose U hx ψ' P hP α β hα hβ he using
    finitePresentation_local_comparison X F r ψ hψ
  have hgen (x : X) : ∃ G : ((kernel ψ).over (U x)).GeneratingSections,
      G.IsFiniteType := by
    let := hP x
    obtain ⟨G, hG⟩ := finitePresentation_kernel_comparison_generators
      X (U x) (F.over (U x)) (P x) r (ψ' x) (α x) (β x) (hα x) (hβ x)
    let := hG
    exact ⟨G.ofEpi (he x).some.inv, inferInstance⟩
  choose G hG using hgen
  let σ : (kernel ψ).LocalGeneratorsData :=
    { I := X
      X := U
      coversTop := (Opens.coversTop_iff _ U).mpr (by
        apply eq_top_iff.mpr
        intro x _
        exact Opens.mem_iSup.mpr ⟨x, hx x⟩)
      generators := G }
  have hσ : σ.IsFiniteType := by
    constructor
    intro x
    exact hG x
  apply SheafOfModules.IsFiniteType.mk
  exact ⟨σ, hσ⟩

end AlgebraicGeometry.RingedSpace
