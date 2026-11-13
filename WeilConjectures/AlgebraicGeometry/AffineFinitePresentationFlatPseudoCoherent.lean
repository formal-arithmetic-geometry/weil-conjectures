/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.RingTheory.FiniteProjectiveComplexFreeModel

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A bounded-above finite-presentation flat quasi-coherent complex on an affine
scheme has pseudo-coherent global sections (Stacks, Tags 064U and 08EB). -/
theorem affine_finitePresentation_flat_pseudoCoherent (S : Scheme.{u})
    (hS : IsAffine S) (D : CochainComplex S.Modules ℤ) (b : ℕ)
    (hDle : D.IsStrictlyLE b)
    (hDflat : ∀ n : ℤ, (D.X n).IsFlatOver (𝟙 S))
    (hDqc : ∀ n : ℤ, (D.X n).IsQuasicoherent)
    (hDfp : ∀ n : ℤ, (D.X n).IsFinitePresentation) :
      (letI : CommRing (S.ringCatSheaf.obj.obj (.op ⊤)) :=
        inferInstanceAs (CommRing Γ(S, ⊤));
        letI := HasDerivedCategory.standard (ModuleCat.{u} (S.ringCatSheaf.obj.obj (.op ⊤)));
        DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj
          (((SheafOfModules.evaluation.{u} S.ringCatSheaf (.op ⊤)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj D))) := by
  have := hS
  let A := S.ringCatSheaf.obj.obj (.op ⊤)
  let : CommRing A := inferInstanceAs (CommRing Γ(S, ⊤))
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let P : CochainComplex (ModuleCat.{u} A) ℤ :=
    ((SheafOfModules.evaluation.{u} S.ringCatSheaf (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj D
  have hPbound : P.IsStrictlyLE (b : ℤ) := by
    have := hDle
    exact inferInstance
  have hterms : ∀ n : ℤ, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n) := by
    intro n
    change Module.Finite Γ(S, ⊤) Γ(D.X n, ⊤) ∧
      Module.Projective Γ(S, ⊤) Γ(D.X n, ⊤)
    have := hDqc n
    have := hDfp n
    have hfp : Module.FinitePresentation Γ(S, ⊤) Γ(D.X n, ⊤) :=
      finitePresentation_sections_of_isFinitePresentation (D.X n) (isAffineOpen_top S)
    have hflat := hDflat n ⟨⊤, isAffineOpen_top S⟩ ⟨⊤, isAffineOpen_top S⟩ (by simp)
    have he : Scheme.Hom.appLE (𝟙 S) ⊤ ⊤ (by simp) = 𝟙 Γ(S, ⊤) := by
      simp [Scheme.Hom.appLE]
    dsimp only at hflat
    rw [he] at hflat
    change Module.Flat Γ(S, ⊤) Γ(D.X n, ⊤) at hflat
    have : Module.Flat Γ(S, ⊤) Γ(D.X n, ⊤) := hflat
    exact ⟨inferInstanceAs (Module.Finite Γ(S, ⊤) Γ(D.X n, ⊤)),
      Module.Flat.projective_of_finitePresentation⟩
  obtain ⟨F, hFbound, hFfree, f, hf⟩ :=
    CochainComplex.exists_finiteFree_model_of_finite_projective A P (b : ℤ) hPbound
      (fun n ↦ (hterms n).1) (fun n ↦ (hterms n).2)
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) f).mpr hf
  exact ⟨F, (b : ℤ), hFbound, hFfree, ⟨asIso (DerivedCategory.Q.map f)⟩⟩

end AlgebraicGeometry.Scheme.Modules
