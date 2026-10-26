/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ComponentExchangeFactor
public import WeilConjectures.TraceFormula.Specialization.CompactificationRouteClosedExtension
public import WeilConjectures.TraceFormula.Specialization.DeformationUnitClass
public import WeilConjectures.TraceFormula.Specialization.PointExchangeOnComponentBdc

/-!

# The exchange `ν_X` on a proper component, in normal form

Let `x` be a rational point of a separated `k`-scheme `X` of finite type and `g : B ⟶ X` a
morphism from a proper `k`-scheme `B` with a rational point `b` such that `b ≫ g = x`. On
`Rg_* ℚ̄_ℓ`, the compact-support exchange `ν_X = pointCompactSupportExchangeOfSeparated`, read
through `Ra_{X!} Rg_* ≅ Ra_{X!} Rg_! ≅ Ra_{B!}`, is the pushforward exchange `χ_g` of the
deformation models followed by `Ra_{X'!} Rg''_* ≅ Ra_{X'!} Rg''_! ≅ Ra_{B''!}` and the inverse
proper exchange `ν_B` of the deformation of `B` (`deformationCompactSupportExchange`)
(`ProEtale.CondensedRing.pointCompactSupportExchangeOfSeparated_app_lowerStar_normalForm`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] isIso_traitSpecializationUnit

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] (x : RationalPoint X) (k' : Type u) [Field k']
  [Algebra k k'] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] {b : RationalPoint B}
  [IsProper (deformationTotalToTrait B b.left.ker k')] (g : B ⟶ X) (hbg : b ≫ g = x)
  [IsProper g.left]
  [IsProper (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k').left]

/-- **`ν_X` on a proper component, in normal form**: on `Rg_* ℚ̄_ℓ` for `g : B ⟶ X` from a proper
`B` with `b ≫ g = x`, the exchange `ν_X` followed by `Ψ_s(Ra_{X!} Rg_* ≅ Ra_{X!} Rg_! ≅ Ra_{B!})`
is `Ra_{X'!}(χ_g)` followed by `Ra_{X'!} Rg''_* ≅ Ra_{X'!} Rg''_! ≅ Ra_{B''!}` and the inverse
proper exchange `ν_B` of the deformation of `B`. -/
theorem pointCompactSupportExchangeOfSeparated_app_lowerStar_normalForm :
    (pointCompactSupportExchangeOfSeparated (ℓ := ℓ) x k').app
        ((boundedConstructibleLowerStar ℓ g).obj (𝟙_ _)) ≫
      (traitSpecialization k k').map
        ((boundedConstructibleLowerShriek ℓ (toPoint X)).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app (𝟙_ _)) ≫
          (lowerShriekCompOfEq ℓ g (toPoint X) (comp_toPoint g)).inv.app (𝟙_ _)) =
    (boundedConstructibleLowerShriek ℓ (toPoint (deformationSpecialFibre X x.left.ker k'))).map
        (((pointComponentModelHom k' g hbg).boundedConstructiblePushforwardExchange ℓ
            ((deformationModel B b.left.ker k').preservesBoundedConstructible_of_isTraitModel
              (isTraitModel_deformationModel B b.left.ker k')
              (deformationModel_exists_comp_ε B _ k'))
            ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
              (isTraitModel_deformationModel X x.left.ker k')
              (deformationModel_exists_comp_ε X _ k'))).app (𝟙_ _)) ≫
      ((boundedConstructibleLowerShriek ℓ (toPoint (deformationSpecialFibre X x.left.ker k'))).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
            (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k')).inv.app _) ≫
        (lowerShriekCompOfEq ℓ
          (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k')
          (toPoint (deformationSpecialFibre X x.left.ker k')) (comp_toPoint _)).inv.app _ ≫
        (deformationCompactSupportExchange B b.left.ker k').app (𝟙_ _)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
