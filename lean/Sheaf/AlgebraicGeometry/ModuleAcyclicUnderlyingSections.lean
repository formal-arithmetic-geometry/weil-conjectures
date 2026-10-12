module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale

/-- Forgetting coefficients preserves bijectivity of restriction on global sections.
Source: Stacks Project, Tag 03FD (forgetting coefficients) and Tag 095T, paragraph 2.
(blueprint: new-module-acyclic-underlying-sections)

Proof: The forgetful functor from modules to abelian groups preserves limits and
colimits. It therefore commutes with the sheafification construction of inverse
image. This gives the canonical natural isomorphism U(i^* M) ≅ i^* U(M).
Evaluation at the terminal site object and the global-sections/terminal-sections
isomorphisms identify the underlying group of Γ(M) with Γ(U(M)), and similarly on Y.
Naturality of the inverse-image adjunction unit identifies the restriction maps
under these comparisons. The given module isomorphism has a two-sided inverse;
forget its scalar structure and conjugate by the comparison isomorphisms to obtain
an inverse of the displayed abelian restriction. This also applies to the zero sheaf. -/
theorem Etale.bijective_underlying_globalSectionsUpperStarMap
    {X Y : Scheme.{u}} (i : Y ⟶ X) (r : ℕ)
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    (h : IsIso (globalSectionsUpperStarMap
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) i M)) :
    Function.Bijective (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} i
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
        AddCommGrpCat.{u + 1})).obj M)) := by sorry

end AlgebraicGeometry
