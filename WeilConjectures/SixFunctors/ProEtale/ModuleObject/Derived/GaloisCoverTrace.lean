/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.GaloisCoverTraceMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldLinear

/-!
# The derived trace of a finite étale Galois covering

Let `Λ` be a commutative condensed ring and `g : Y ⟶ X` a finite étale morphism with a Galois
action of a finite group `Γ` (`AlgebraicGeometry.ProEtale.IsGaloisAction`). The pushforward
`g_*` of module objects is exact, so the derived adjunction `Lg^* ⊣ Rg_*`
(`AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`) carries the
derived trace `Lg^* ⋙ Rg_* ⟶ 𝟭` and the derived action of `Γ`
(`AlgebraicGeometry.ProEtale.CondensedRing.derivedGaloisTrace`,
`AlgebraicGeometry.ProEtale.CondensedRing.derivedGaloisAction`), with

* `u ≫ t = |Γ| • 𝟙`
  (`AlgebraicGeometry.ProEtale.CondensedRing.derivedUnit_comp_derivedGaloisTrace`),
* `t ≫ u = ∑ a, ρ a`
  (`AlgebraicGeometry.ProEtale.CondensedRing.derivedGaloisTrace_comp_derivedUnit`).

Hence, when multiplication by `|Γ|` is invertible on `G ∈ D(Mod_{Λ_X})`, the derived unit
`G ⟶ Rg_* Lg^* G` is a split monomorphism, split by the normalized trace, and its idempotent is
the average of the action of `Γ`
(`AlgebraicGeometry.ProEtale.CondensedRing.derivedUnit_comp_normalizedTrace`,
`AlgebraicGeometry.ProEtale.CondensedRing.nsmul_normalizedTrace_comp_derivedUnit`). Multiplication
by `|Γ|` is invertible as soon as `|Γ|` is a unit in a ring of constants of `Λ`
(`AlgebraicGeometry.ProEtale.CondensedRing.isIso_nsmul_id_of_isUnit`); this covers `ℚ̄_ℓ`, finite
extensions `E` of `ℚ_ℓ`, `𝒪_E` and finite rings `Λ` when `|Γ|` is a power of `p ≠ ℓ`
(`AlgebraicGeometry.ProEtale.CondensedRing.isIso_nsmul_id_padicAlgCl`,
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_nsmul_id_padicSubfield`).
-/

@[expose] public section

universe u

open CategoryTheory Category Abelian Limits MonoidalCategory MonObj

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (g : Y ⟶ X) [IsFinite g] [Etale g] [Surjective g]
  {Γ : Type u} {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ i, ρ i ≫ g = g)
  [Group Γ] [Fintype Γ] (hmul : ∀ a b, ρ a ≫ ρ b = ρ (a * b)) (hgal : IsGaloisAction g ρ)

instance : PreservesFiniteColimits (g)_*⟦Λ⟧ := preservesFiniteColimits_lowerStar_of_isFinite Λ g

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing
