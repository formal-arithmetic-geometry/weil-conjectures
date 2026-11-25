/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModule
import WeilConjectures.ConstructibleSheaf.TorsorDiagonalEvaluation
import WeilConjectures.ConstructibleSheaf.TorsorInvariantSections
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Pullback and coefficient comparisons for associated module sheaves

For a connected Galois cover `c` with finite group `P` of a connected scheme, the pullback along
`c` of the module sheaf associated with a representation of `P` is the constant sheaf on the
underlying module, and the module sheaf associated with the trivial representation is the
constant sheaf
(`AlgebraicGeometry.Scheme.GaloisCover.associatedModuleFunctor_comparisons`).

## References

* Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

set_option backward.isDefEq.respectTransparency false in
/-- The associated module sheaf functor `T` of a connected Galois cover `c` satisfies two
comparisons: `T ⋙ c.π^*` is naturally isomorphic to taking the constant sheaf on the
underlying module of a representation, and `T` sends the trivial representation on
`ZMod ℓ` to the constant sheaf `ZMod ℓ` on `V`. -/
theorem Scheme.GaloisCover.associatedModuleFunctor_comparisons
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P] :
    let C := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))
    let T := c.associatedModuleFunctor ℓ
    Nonempty (T ⋙ (c.π)^*[C] ≅
      forget₂ (Rep.{u + 1} (ZMod ℓ) P) (ModuleCat.{u + 1} (ZMod ℓ)) ⋙
        ModuleCat.restrictScalars.{u + 1}
          (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ) ⋙
        constantSheaf c.P.smallEtaleTopology C) ∧
    Nonempty (T.obj (Rep.trivial (ZMod ℓ) P (ULift.{u + 1} (ZMod ℓ))) ≅
      (constantSheaf V.smallEtaleTopology C).obj
        (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))) := by
  dsimp only
  let C := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))
  let S := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ)
  let F := c.equivariantModulePresheafFunctor ℓ ⋙
    (Functor.whiskeringRight V.Etaleᵒᵖ _ _).obj S
  let T := c.associatedModuleFunctor ℓ
  obtain ⟨d⟩ := c.equivariantModulePresheaf_diagonal ℓ
  obtain ⟨t⟩ := c.equivariantModulePresheaf_trivial ℓ
  constructor
  · let R := Etale.localizationRestriction C c.π c.etale
    let K := forget₂ (Rep.{u + 1} (ZMod ℓ) P) (ModuleCat.{u + 1} (ZMod ℓ)) ⋙
      S ⋙ constantSheaf c.P.smallEtaleTopology C
    have h : T ⋙ R ≅ K :=
      (Functor.isoWhiskerLeft F
        ((MorphismProperty.Over.map ⊤ c.etale).pushforwardContinuousSheafificationCompatibility
          C (c.P.smallGrothendieckTopology @Etale)
            (V.smallGrothendieckTopology @Etale)).symm) ≪≫
      Functor.isoWhiskerRight d (presheafToSheaf c.P.smallEtaleTopology C) ≪≫
      Functor.isoWhiskerLeft K (sheafificationNatIso c.P.smallEtaleTopology C).symm
    exact ⟨Functor.isoWhiskerLeft T
      (Etale.upperStarIsoLocalizationRestriction C c.π c.etale) ≪≫
      h⟩
  · exact ⟨(presheafToSheaf V.smallEtaleTopology C).mapIso t ≪≫
      (sheafificationIso ((constantSheaf V.smallEtaleTopology C).obj
        (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))).symm⟩

end AlgebraicGeometry
