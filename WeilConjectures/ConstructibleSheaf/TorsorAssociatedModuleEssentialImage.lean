/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModule
import WeilConjectures.ConstructibleSheaf.TorsorSectionEvaluation
import WeilConjectures.ConstructibleSheaf.TorsorSectionEvaluationBijective

/-!
# The essential image of the associated module functor

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- Every module sheaf made constant by the torsor is an associated sheaf.
Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS. -/
theorem Scheme.GaloisCover.associatedModuleFunctor_essentialImage
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj A)) :
    ∃ N : Rep.{u + 1} (ZMod ℓ) P, Nonempty ((c.associatedModuleFunctor ℓ).obj N ≅ F) := by
  obtain ⟨α, hα⟩ := c.exists_sectionEvaluation ℓ P F A h
  have hbij (W : V.Etaleᵒᵖ) : Function.Bijective (α.app W) :=
    c.sectionEvaluation_bijective ℓ P F A h α hα W
  have (W : V.Etaleᵒᵖ) : IsIso (α.app W) :=
    (ConcreteCategory.isIso_iff_bijective (α.app W)).2 (hbij W)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let e := (presheafToSheaf V.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).mapIso (asIso α).symm
  let ε := asIso ((sheafificationAdjunction V.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).counit.app F)
  exact ⟨c.sectionRepresentation ℓ F, ⟨e ≪≫ ε⟩⟩

end AlgebraicGeometry
