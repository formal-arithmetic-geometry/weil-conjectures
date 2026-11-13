/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients

/-! # Integral coefficients and open extension by zero

Source: Stacks Project, Tags 03S5 and 0GJA. -/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- The canonical integral coefficient encoding commutes with restriction followed by
extension by zero along an open immersion.
Source: Stacks Project, Tag 03S5 (extension by zero), and Tag 0GJA, proof. -/
theorem integral_open_extension_comparison {X : Scheme.{u}}
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : X.Opens) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let F := (sheafCompose X.smallEtaleTopology E).obj A
    let B := (openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
      ((upperStar AddCommGrpCat.{u + 1} U.ι).obj A)
    Nonempty ((sheafCompose X.smallEtaleTopology E).obj B ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι).obj
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι).obj F)) := by
  let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
  have : Limits.PreservesLimitsOfSize.{u + 1, u + 1} E := inferInstance
  have : Limits.PreservesColimitsOfSize.{u + 1, u + 1} E := inferInstance
  have : X.smallEtaleTopology.PreservesSheafification E :=
    GrothendieckTopology.instPreservesSheafification X.smallEtaleTopology E
  let L := (MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ U.ι)).op
  let R := openImmersionRestriction AddCommGrpCat.{u + 1} U.ι
  let S := openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι
  let F := (sheafCompose X.smallEtaleTopology E).obj A
  let e₁ := (sheafComposeNatIso X.smallEtaleTopology E
    (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (sheafificationAdjunction X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))).app (L.lan.obj (R.obj A).obj)
  let e₂ := (presheafToSheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapIso
      ((E.lanCompIsoOfPreserves L).app (R.obj A).obj)
  let e₃ : (sheafCompose U.toScheme.smallEtaleTopology E).obj (R.obj A) ≅ S.obj F :=
    Iso.refl _
  let e₄ := (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι).mapIso
    ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      U.ι).app F)
  let e₀ := (sheafCompose X.smallEtaleTopology E).mapIso
    ((openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).mapIso
      ((upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} U.ι).app A))
  exact ⟨e₀ ≪≫ e₁.symm ≪≫ e₂ ≪≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι).mapIso e₃ ≪≫
      e₄.symm⟩


end AlgebraicGeometry.Etale
