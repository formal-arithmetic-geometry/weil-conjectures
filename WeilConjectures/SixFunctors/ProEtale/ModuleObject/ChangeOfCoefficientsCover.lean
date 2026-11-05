/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-!
# Checking that a morphism out of an extension of scalars is invertible on a pro-étale cover

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, `S` a scheme, `K` a module object
over `Λ_S`, `L` one over `Λ'_S` and `φ : K ⟶ Res L` a `Λ_S`-linear map, with adjoint
`φ♯ : Λ'_S ⊗_{Λ_S} K ⟶ L`. Then:

* the pullbacks of module objects along the members of a pro-étale cover are jointly
  conservative (`ProEtale.CondensedRing.isIso_of_isIso_upperStar_map_of_cover`);
* the pullback of `φ♯` along `f` is, through the (Pull) isomorphism
  `f^* (Λ'_S ⊗ K) ≅ Λ'_Y ⊗ f^* K`, the adjoint of `f^* φ` followed by `f^* Res L ≅ Res f^* L`
  (`ProEtale.CondensedRing.pullIso_hom_app_comp_upperStar_map_homEquiv_symm`);
* hence `φ♯` is invertible as soon as all these adjoints are, for a pro-étale cover
  (`ProEtale.CondensedRing.isIso_homEquiv_symm_of_cover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Conservative

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Pullbacks of module objects along a pro-étale cover are jointly conservative.** -/
theorem isIso_of_isIso_upperStar_map_of_cover {S : Scheme.{u}}
    {N N' : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)} (g : N ⟶ N')
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S)
    (h : ∀ i, IsIso ((𝒰.f i)^*⟦Λ⟧.map g)) : IsIso g := by
  have hw (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  have : IsIso g.hom := by
    refine ProEtale.isIso_of_isIso_localizationRestriction Ab.{u + 1} g.hom 𝒰.f 𝒰.mem₀
      fun i ↦ ?_
    have h₁ : IsIso ((Mod.forget _).map ((𝒰.f i)^*⟦Λ⟧.map g)) := inferInstance
    have h₂ := (NatIso.isIso_map_iff (upperStarForgetIso Λ (𝒰.f i)) g).2 h₁
    exact (NatIso.isIso_map_iff
      (ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} (𝒰.f i) inferInstance) g.hom).1 h₂
  have : IsIso ((Mod.forget _).map g) := this
  exact isIso_of_reflects_iso g (Mod.forget _)

end Conservative

section Adjoint

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

end Adjoint

end AlgebraicGeometry.ProEtale.CondensedRing
