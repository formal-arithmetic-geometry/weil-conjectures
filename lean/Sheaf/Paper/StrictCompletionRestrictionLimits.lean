/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module
public import Sheaf.Paper.StrictCompletionRestrictionData
import all Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
/-! # StrictCompletionRestrictionLimits -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
universe u
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction
private theorem weaklyEtale_limits {X Y : Scheme.{u}} (f : X ⟶ Y) [hf : WeaklyEtale f] :
    PreservesLimitsOfSize.{u + 1, u + 1} (ProEtale.upperStar Ab.{u + 1} f) := by
  let := Scheme.ProEt.isContinuous_overMap hf
  let : PreservesLimitsOfSize.{u + 1, u + 1}
      (localizationRestriction Ab.{u + 1} f hf ⋙ sheafToPresheaf _ _) :=
    preservesLimits_of_natIso (Functor.sheafPushforwardContinuousCompSheafToPresheafIso
      _ _ _ _).symm
  let : PreservesLimitsOfSize.{u + 1, u + 1} (localizationRestriction Ab.{u + 1} f hf) :=
    preservesLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  exact preservesLimits_of_natIso (upperStarIsoLocalizationRestriction _ f hf).symm

private theorem module_limits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [PreservesLimitsOfSize.{u + 1, u + 1} (ProEtale.upperStar Ab.{u + 1} f)] :
    PreservesLimitsOfSize.{u + 1, u + 1} (CondensedRing.upperStar Λ f) := by
  let : MonObj (condensedRingObj Λ X) := (upperStarFromPoint X).monObjObj Λ
  let F := ProEtale.upperStar Ab.{u + 1} f
  let : F.Monoidal := inferInstanceAs (ProEtale.upperStar Ab.{u + 1} f).Monoidal
  let R := condensedRingObj Λ Y
  let : MonObj R := (upperStarFromPoint Y).monObjObj Λ
  let : MonObj (F.obj R) := F.monObjObj R
  let : PreservesLimitsOfSize.{u + 1, u + 1} (F.mapMod R ⋙ (Mod.forget (F.obj R) :
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (F.obj R) ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})) :=
    inferInstanceAs (PreservesLimitsOfSize.{u + 1, u + 1} (Mod.forget R ⋙ F))
  let : ReflectsLimitsOfSize.{u + 1, u + 1} ((Mod.forget (F.obj R) :
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (F.obj R) ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})) :=
    reflectsLimits_of_reflectsIsomorphisms
  let : PreservesLimitsOfSize.{u + 1, u + 1} (F.mapMod R) :=
    preservesLimits_of_reflects_of_preserves _
      ((Mod.forget (F.obj R) :
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (F.obj R) ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}))
  let : PreservesLimitsOfSize.{u + 1, u + 1}
      (Mod.extendScalars (condensedPullbackHom Λ f)) :=
    preservesLimits_of_natIso (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).symm
  exact inferInstanceAs (PreservesLimitsOfSize.{u + 1, u + 1}
    (F.mapMod R ⋙ Mod.extendScalars (condensedPullbackHom Λ f)))

/-- Inverse image along the multiplicative closure of immersions and weakly etale
maps preserves all limits in the coefficient universe.

Source: Stacks Tag 09AA and the localized-site description, Tags 00Y0 and 03DB
(blueprint: lem-sfb-strict-completion-restriction-limits).

Proof: For weakly etale maps identify inverse image with localized restriction.
Its composite with the sheaf inclusion preserves limits, and the inclusion reflects
them. For immersions use the immersion limit-preservation theorem. Limits of internal
modules are detected on underlying sheaves; extension along the coefficient isomorphism
is equivalent to restriction along its inverse, and preserves limits. The canonical
composition isomorphism proves the multiplicative-closure induction, including identity. -/
theorem strictCompletionRestrictionLimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : (MorphismProperty.multiplicativeClosure
      (fun {V W : Scheme.{u}} (g : V ⟶ W) ↦ IsImmersion g ∨ WeaklyEtale g)) f) :
    PreservesLimitsOfSize.{u + 1, u + 1} (CondensedRing.upperStar Λ f) := by
  have hbasic {V W : Scheme.{u}} (g : V ⟶ W) (hg : IsImmersion g ∨ WeaklyEtale g) :
      PreservesLimitsOfSize.{u + 1, u + 1} (CondensedRing.upperStar Λ g) := by
    rcases hg with hg | hg
    · let := hg
      let : PreservesLimitsOfSize.{u + 1, u + 1} (ProEtale.upperStar Ab.{u + 1} g) :=
        (Scheme.proEtale_immersion_inverseImage_preservesLimits g).2.1
      exact module_limits Λ g
    · let := hg
      let := weaklyEtale_limits g
      exact module_limits Λ g
  induction hf with
  | of f h => exact hbasic f h
  | id X =>
      let := weaklyEtale_limits (𝟙 X)
      exact module_limits Λ (𝟙 X)
  | comp_of f g hf hg ih =>
      let := ih
      let := hbasic g hg
      exact preservesLimits_of_natIso (CondensedRing.upperStarComp Λ f g).symm
end AlgebraicGeometry.ProEtale.StrictCompletionRestriction
