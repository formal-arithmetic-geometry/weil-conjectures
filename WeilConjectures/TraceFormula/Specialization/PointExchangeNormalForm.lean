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
public import WeilConjectures.TraceFormula.Specialization.PointExchangeNormalFormAux
public import WeilConjectures.Tactic.AssignModProofs

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

set_option maxHeartbeats 4000000 in
-- the instance of `pointNormalForm_aux'` at the concrete composites is slow to elaborate
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
  have hF1 := pointCompactSupportExchangeOfSeparated_app_lowerStar_component_eq x k' g hbg
    (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  have hPB := (deformationModel B b.left.ker k').preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel B b.left.ker k') (deformationModel_exists_comp_ε B _ k')
  have hPX := (deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel X x.left.ker k') (deformationModel_exists_comp_ε X _ k')
  have hPT := (traitModel k k').preservesBoundedConstructible_of_isTraitModel (ℓ := ℓ)
    (isTraitModel_traitModel k k') ⟨traitToBase k k', traitModel_j_traitToBase k k'⟩
  have : IsProper (toPoint B).left := by rw [toPoint_left]; infer_instance
  have : IsProper (toPoint (deformationSpecialFibre B b.left.ker k')).left := by
    rw [toPoint_left]; infer_instance
  have hνB := deformationCompactSupportExchange_app_comp B b.left.ker k' (ℓ := ℓ)
    (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  have hχg := NearbyCyclesModel.Hom.ι_map_boundedConstructiblePushforwardExchange_app ℓ
    (pointComponentModelHom k' g hbg) hPB hPX (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  -- the source route
  have := isProper_left_of_isProper_of_isSeparated (g ≫ (compactificationOverField (toPoint X)).overI)
  have : IsProper (toPoint (compactificationOverField (toPoint X)).overObj).left := by
    rw [toPoint_left]; infer_instance
  have := isProper_left_of_isProper_of_isSeparated
    ((g ≫ (compactificationOverField (toPoint X)).overI) ≫
      toPoint (compactificationOverField (toPoint X)).overObj)
  have := isProper_left_of_isProper_of_isSeparated (g ≫ toPoint X)
  have hS := pointRoute_source_eq ℓ g (compactificationOverField (toPoint X)).overI
    (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  -- the target route
  have := isProper_left_of_isProper_of_isSeparated
    (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k' ≫
      pointSpecialMap x (compactificationOverField (toPoint X)).overI k')
  have : IsProper (toPoint (compactifiedSpecialFibre (compactificationOverField (toPoint X)).overObj
      (x ≫ (compactificationOverField (toPoint X)).overI) k')).left := by
    rw [toPoint_left]; infer_instance
  have := isProper_left_of_isProper_of_isSeparated
    ((deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k' ≫
      pointSpecialMap x (compactificationOverField (toPoint X)).overI k') ≫
      toPoint (deformationSpecialFibre (compactificationOverField (toPoint X)).overObj
        (x ≫ (compactificationOverField (toPoint X)).overI).left.ker k'))
  have := isProper_left_of_isProper_of_isSeparated
    ((deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k' ≫
      pointSpecialMap x (compactificationOverField (toPoint X)).overI k') ≫
      deformationSpecialFibreToCompactified (compactificationOverField (toPoint X)).overObj
        (x ≫ (compactificationOverField (toPoint X)).overI) k')
  have := isProper_left_of_isProper_of_isSeparated
    (((deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k' ≫
      pointSpecialMap x (compactificationOverField (toPoint X)).overI k') ≫
      deformationSpecialFibreToCompactified (compactificationOverField (toPoint X)).overObj
        (x ≫ (compactificationOverField (toPoint X)).overI) k') ≫
      toPoint (compactifiedSpecialFibre (compactificationOverField (toPoint X)).overObj
        (x ≫ (compactificationOverField (toPoint X)).overI) k'))
  have hT := pointRoute_target_eq ℓ
    (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k')
    (pointSpecialMap x (compactificationOverField (toPoint X)).overI k')
    (deformationSpecialFibreToCompactified (compactificationOverField (toPoint X)).overObj
        (x ≫ (compactificationOverField (toPoint X)).overI) k')
    ((NearbyCyclesModel.boundedConstructibleNearbyCycles hPB).obj
      (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
  have hχB : Mono (((deformationToTraitModelHom B b.left.ker k').boundedConstructiblePushforwardExchange
      ℓ hPB hPT).app (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) := by
    have := NearbyCyclesModel.Hom.isIso_boundedConstructiblePushforwardExchange_of_isProper
      (deformationToTraitModelHom B b.left.ker k') hPB hPT
      (isPullback_deformationSpecialFibre_toPoint B _ k') (isPullback_deformationModel_ε_toPoint B _ k')
    infer_instance
  refine CategoryTheory.pointNormalForm_aux' _
    (ObjectProperty.fullyFaithfulι _).faithful _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF1
    (boundedConstructibleLowerStarCompatibility ℓ
      (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k'))
    (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hPB)
    ((pointComponentModelHom k' g hbg).boundedConstructiblePushforwardExchange ℓ hPB hPX)
    ?hχg
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint B))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
      (toPoint (deformationSpecialFibre B b.left.ker k')))
    ((deformationToTraitModelHom B b.left.ker k').boundedConstructiblePushforwardExchange ℓ hPB hPT)
    ?hχB
    (deformationCompactSupportExchange B b.left.ker k')
    ?hνB
    ((boundedConstructibleLowerShriek ℓ (toPoint X)).map
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app (𝟙_ _)))
    ((lowerShriekCompOfEq ℓ g (toPoint X) (comp_toPoint g)).inv.app (𝟙_ _))
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
      (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k')).inv.app _)
    ((lowerShriekCompOfEq ℓ
      (deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k')
      (toPoint (deformationSpecialFibre X x.left.ker k')) (comp_toPoint _)).inv.app _)
    (eqToHom ?es) (eqToHom ?et) ?hS ?hT ?hχ rfl
  case es => rw [pointRoute_left_eq]; rfl
  case et => rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, comp_toPoint]; rfl
  case hχg => assign_mod_proofs hχg
  case hχB => assign_mod_proofs hχB
  case hνB => assign_mod_proofs hνB
  case hS => assign_mod_proofs hS
  case hT => assign_mod_proofs hT
  case hχ =>
    have hmap := NearbyCyclesModel.Hom.ι_map_boundedConstructiblePushforwardExchange_app ℓ
      (deformationToTraitModelHom B b.left.ker k') hPB hPT
      (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    refine CategoryTheory.pointNormalForm_hχ_aux
      (cRB := boundedConstructibleLowerStarCompatibility ℓ (toPoint B))
      (cRB' := boundedConstructibleLowerStarCompatibility ℓ
        (toPoint (deformationSpecialFibre B b.left.ker k')))
      (χBa := (deformationToTraitModelHom B b.left.ker k').pushforwardExchange
        (Profinite.padicAlgClRingObj ℓ))
      (hmap := ?hmap) (h := ?h) (h' := ?h') (h'' := ?h'') (heq := ?heq) (hs := ?hs) (ht := ?ht)
    case h => rw [pointRoute_left_eq]
    case h' => rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, comp_toPoint]
    case h'' => rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, comp_toPoint]
    case hmap => assign_mod_proofs hmap
    case heq =>
      have heq0 := NearbyCyclesModel.Hom.pushforwardExchange_app_eq_of_eq
        (Profinite.padicAlgClRingObj ℓ)
        (pointCompModelHom x (compactificationOverField (toPoint X)).overI k'
          (pointComponentModelHom k' g hbg))
        (deformationToTraitModelHom B b.left.ker k')
        (pointRoute_left_eq g (compactificationOverField (toPoint X)).overI)
        (by rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, comp_toPoint])
        (pointComponentCompModelHom_total_eq x k' g hbg
          (compactificationOverField (toPoint X)).overI)
        (pointComponentCompModelHom_generic_eq x k' g hbg
          (compactificationOverField (toPoint X)).overI)
        (@CategoryTheory.Functor.obj (Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) _ _ _
          (@CategoryTheory.ObjectProperty.ι _ _
            (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) B.left)))
          (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
      assign_mod_proofs heq0
    case hs =>
      have hs0 := eqToHom_comp_lowerStarCompatibility_hom ℓ (toPoint B)
        (pointRoute_left_eq g (compactificationOverField (toPoint X)).overI)
        (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
      assign_mod_proofs hs0
    case ht =>
      have ht0 := map_comp_eqToHom_lowerStarCompatibility ℓ
        (toPoint (deformationSpecialFibre B b.left.ker k'))
        (f₁ := (((deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k').left ≫
          (pointSpecialMap x (compactificationOverField (toPoint X)).overI k').left) ≫
          (deformationSpecialFibreToCompactified (compactificationOverField (toPoint X)).overObj
            (x ≫ (compactificationOverField (toPoint X)).overI) k').left) ≫
          (toPoint (compactifiedSpecialFibre (compactificationOverField (toPoint X)).overObj
            (x ≫ (compactificationOverField (toPoint X)).overI) k')).left)
        (by rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, comp_toPoint])
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hPB).obj
          (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
        ((NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hPB).inv.app
          (𝟙_ Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
      assign_mod_proofs ht0

end AlgebraicGeometry.ProEtale.CondensedRing
