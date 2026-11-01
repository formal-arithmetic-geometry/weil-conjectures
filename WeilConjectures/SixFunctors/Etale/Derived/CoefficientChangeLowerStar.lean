/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange

/-!
# The proper direct image carries derived base changes to derived base changes

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings with `Λ` finite and `p : Z ⟶ Y` a proper
morphism. If `η : K ⟶ Res K'` exhibits `K'` as the derived base change `K ⊗ᴸ_Λ Λ'`, then
`Rp_* η`, followed by the coefficient comparison `Rp_* Res ≅ Res Rp_*`
(`AlgebraicGeometry.Etale.derivedRestrictScalarsCompRightDerivedLowerStarIso`), exhibits
`Rp_* K'` as `Rp_* K ⊗ᴸ_Λ Λ'`
(`AlgebraicGeometry.Etale.isDerivedBaseChange_rightDerivedLowerStar_map_comp`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- **The proper direct image carries derived base changes to derived base changes.** For a
finite coefficient ring `Λ`, a morphism `ρ : Λ →+* Λ'` and a proper `p : Z ⟶ Y`, if
`η : K ⟶ Res K'` exhibits `K'` as `K ⊗ᴸ_Λ Λ'`, then `Rp_* η` followed by the comparison
`Rp_* Res ≅ Res Rp_*` exhibits `Rp_* K'` as `Rp_* K ⊗ᴸ_Λ Λ'`. -/
theorem isDerivedBaseChange_rightDerivedLowerStar_map_comp [Finite Λ] {Z Y : Scheme.{u}}
    (p : Z ⟶ Y) [IsProper p] (d : ℕ)
    (hd : ∀ (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      Limits.IsZero ((((p)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    {K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    {η : K ⟶ (Sheaf.derivedRestrictScalars Z.smallEtaleTopology ρ).obj K'}
    (hη : Sheaf.IsDerivedBaseChange η) :
    Sheaf.IsDerivedBaseChange ((R((p)_*[ModuleCat.{u + 1} Λ])).map η ≫
      (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ p d hd).hom.app K') :=
  sorry

end AlgebraicGeometry.Etale
