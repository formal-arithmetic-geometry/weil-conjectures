/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Local lifts of presentations of a finite constant quotient

Source: Stacks Project, Tag 093U, extension paragraph.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- A finite constant quotient admits a module presentation whose constant sheaf map
lifts locally to the middle term of the extension.

Source: Stacks Project, Tag 093U, extension paragraph, through the choice of lifted generators.
(blueprint: lem-pc-constant-extension-presentation-lift)

Proof: On a nonempty base, a constant model N of the quotient has a stalk isomorphic
to N. The finite-stalk assumption therefore makes N finitely generated. Choose a finite
free surjection P → N, and form its kernel K, giving the module short exact sequence T.
Since the ring and the set of free generators are finite, P and its subset K are finite
sets. The finite set of all elements of K generates it, so K is finitely generated.
The generators of P map to sections of the quotient. Local surjectivity of the sheaf
epimorphism lifts each section on an etale cover; a finite common refinement lifts them
simultaneously. By the universal property of the constant free sheaf these lifts define r.
Its composite with the quotient map equals the constant presentation map, since the two
maps agree on the free generators. Constant sheaves commute with etale restriction,
which supplies e and the displayed identity. For an empty base use the empty cover. -/
theorem exists_constantExtension_presentation_lift {X : Scheme.{u}}
    {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hS : S.ShortExact) [S.X₃.IsConstant X.smallEtaleTopology]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i,
      ∃ T : ShortComplex (ModuleCat.{u + 1} Λ), T.ShortExact ∧ Module.Finite Λ T.X₁ ∧
        ∃ e : (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj T.X₃ ≅
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₃,
        ∃ r : (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj T.X₂ ⟶
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂,
          r ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).map S.g =
            (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map T.g ≫
              e.hom := by sorry

end AlgebraicGeometry.Scheme
