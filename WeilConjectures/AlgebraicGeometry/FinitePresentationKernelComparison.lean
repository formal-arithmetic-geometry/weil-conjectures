/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-! # Finite kernel generators from a comparison of finite free presentations

## References

* Stacks Project, Tag 01BP
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- A finite presentation and two comparison maps generate the kernel of a second
finite free map. (Stacks, Tag 01BP) -/
theorem finitePresentation_kernel_comparison_generators
    (X : RingedSpace.{u}) (U : Opens X)
    (F : SheafOfModules.{u} ((moduleRings X).over U))
    (P : F.Presentation) [P.IsFinite] (r : ℕ)
    (ψ : SheafOfModules.free (R := (moduleRings X).over U) (ULift.{u} (Fin r)) ⟶ F)
    (α : SheafOfModules.free (R := (moduleRings X).over U) (ULift.{u} (Fin r)) ⟶
      SheafOfModules.free P.generators.I)
    (β : SheafOfModules.free (R := (moduleRings X).over U) P.generators.I ⟶
      SheafOfModules.free (ULift.{u} (Fin r)))
    (hα : α ≫ P.generators.π = ψ) (hβ : β ≫ ψ = P.generators.π) :
    ∃ G : (kernel ψ).GeneratingSections, G.IsFiniteType := by
  classical
  let k₁ : kernel P.generators.π ⟶ kernel ψ :=
    kernel.lift ψ (kernel.ι P.generators.π ≫ β) (by simp [hβ])
  let k₂ : SheafOfModules.free (R := (moduleRings X).over U)
      (ULift.{u} (Fin r)) ⟶ kernel ψ :=
    kernel.lift ψ (𝟙 _ - α ≫ β) (by simp [Preadditive.sub_comp, hβ, hα])
  let l : kernel ψ ⟶ kernel P.generators.π :=
    kernel.lift P.generators.π (kernel.ι ψ ≫ α) (by simp [hα])
  have hid : l ≫ k₁ + kernel.ι ψ ≫ k₂ = 𝟙 (kernel ψ) := by
    apply (cancel_mono (kernel.ι ψ)).mp
    simp [k₁, k₂, l, Preadditive.add_comp, Preadditive.comp_sub]
  let M : ULift.{u} Bool → SheafOfModules.{u} ((moduleRings X).over U) :=
    fun b ↦ if b.down then SheafOfModules.free (ULift.{u} (Fin r))
      else kernel P.generators.π
  let d : ∀ b, M b ⟶ kernel ψ := fun b ↦ by
    cases b with
    | up b => cases b
              · exact k₁
              · exact k₂
  let g : ∀ b, (M b).GeneratingSections := fun b ↦ by
    cases b with
    | up b => cases b
              · exact P.relations
              · exact SheafOfModules.GeneratingSections.ofEpiFree (𝟙 _)
  have hg : ∀ b, (g b).IsFiniteType := by
    intro b
    cases b with
    | up b => cases b
              · exact inferInstanceAs P.relations.IsFiniteType
              · exact ⟨inferInstanceAs (Finite (ULift.{u} (Fin r)))⟩
  let p : (∐ M) ⟶ kernel ψ := Sigma.desc d
  have hp : Epi p := by
    have hi : (l ≫ Sigma.ι M ⟨false⟩ + kernel.ι ψ ≫ Sigma.ι M ⟨true⟩) ≫ p =
        𝟙 (kernel ψ) := by
      simpa [p, d, Preadditive.add_comp] using hid
    exact epi_of_epi_fac hi
  have := hp
  refine ⟨(SheafOfModules.GeneratingSections.sigma M g).ofEpi p, ⟨?_⟩⟩
  change Finite (Σ b : ULift.{u} Bool, (g b).I)
  exact @Finite.instSigma _ _ inferInstance (fun b ↦ (hg b).finite)

end AlgebraicGeometry.RingedSpace
