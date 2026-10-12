module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- An extension with constant outer terms admits a local cokernel presentation before
recording finite generation of the source module.
Source: Stacks Project, Tag 093U, extension argument.
(blueprint: lem-pc-constant-extension-cokernel-aux-cover)
-/
theorem exists_constantExtension_cokernelPresentation_aux_cover {X : Scheme.{u}}
    {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hS : S.ShortExact)
    [S.X₁.IsConstant X.smallEtaleTopology] [S.X₃.IsConstant X.smallEtaleTopology]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i,
      ∃ K L : ModuleCat.{u + 1} Λ, ∃ φ :
        (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj K ⟶
          (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj L,
          Nonempty (cokernel φ ≅
            (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂) := by
  sorry

/-- A local presentation can be replaced by one with finitely generated source.
Source: Stacks Project, Tag 093U, finite free presentation step.
(blueprint: lem-pc-constant-extension-cokernel-aux-finite)
-/
theorem finite_cokernelPresentation_of_local_presentation {X : Scheme.{u}}
    {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {𝒰 : Cover.{u} etalePrecoverage X} {i : 𝒰.I₀}
    (h : ∃ K L : ModuleCat.{u + 1} Λ, ∃ φ :
      (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj K ⟶
        (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj L,
      Nonempty (cokernel φ ≅
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂)) :
    ∃ K L : ModuleCat.{u + 1} Λ, Module.Finite Λ K ∧ ∃ φ :
      (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj K ⟶
        (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj L,
      Nonempty (cokernel φ ≅
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂) := by
  sorry

end AlgebraicGeometry.Scheme
