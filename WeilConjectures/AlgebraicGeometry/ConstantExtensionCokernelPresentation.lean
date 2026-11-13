/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.AlgebraicGeometry.ConstantExtensionCokernelAux
import WeilConjectures.AlgebraicGeometry.ConstantExtensionPresentationLift
import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact
import WeilConjectures.AlgebraicGeometry.EtaleShortExactLocalLift
import WeilConjectures.ConstructibleSheaf.Biproduct

/-!
# Cokernel presentations of extensions with finite constant outer terms

Source: Stacks Project, Tag 093U, extension argument.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Locally an extension with finite constant outer terms is a cokernel of a morphism
between constant sheaves, with finitely generated source (Stacks, Tag 093U). -/
theorem exists_constantExtension_cokernelPresentation {X : Scheme.{u}}
    {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hS : S.ShortExact)
    [S.X₁.IsConstant X.smallEtaleTopology] [S.X₃.IsConstant X.smallEtaleTopology]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i,
      ∃ K L : ModuleCat.{u + 1} Λ, Module.Finite Λ K ∧
        ∃ φ : (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj K ⟶
          (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj L,
          Nonempty (cokernel φ ≅ (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂) := by
  obtain ⟨𝒰, h𝒰⟩ := exists_constantExtension_presentation_lift hS
  refine ⟨𝒰, fun i ↦ ?_⟩
  exact finite_cokernelPresentation_of_local_presentation hS (h𝒰 i)

end AlgebraicGeometry.Scheme
