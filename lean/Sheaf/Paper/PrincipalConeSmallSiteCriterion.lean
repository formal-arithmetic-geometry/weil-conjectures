/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module
public import Sheaf.Algebra.Homology.PrincipalConeTower
public import Sheaf.CategoryTheory.RingedPrincipalLocalTests
import Sheaf.Paper.PrincipalConeKoszulRoosComparison
import Sheaf.Paper.PrincipalIdealLocalTestCriterion
import Sheaf.CategoryTheory.RingedKoszulCompletionReflector
import all Sheaf.CategoryTheory.UnitPowerCompleteness

/-! # The principal cone criterion on a small ringed site
Source: Stacks 0999, 099B, 0A0E and 0941.
(blueprint: lem-pur-principal-cone-small-site-criterion). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
set_option hygiene false in
local notation "Rg" => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
set_option hygiene false in
local notation "A" => SheafOfModules.{u} Rg
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
  [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u} ((Rg).over U))]
  [HasExactLimitsOfShape (Discrete ℕ) A]

attribute [local irreducible] CochainComplex.PrincipalCone.completion
  CochainComplex.PrincipalCone.unit
attribute [local irreducible] principalKoszulRoosUnit roosF koszulTowerComplex koszulTensorTower

/-- Singleton Koszul completion is the normalized principal cone completion.
Source: Stacks 0999, 099B, 0A0E and 0941.
(blueprint: lem-pur-principal-cone-small-site-criterion).
Proof: the image ideal of scalar multiplication has precisely the locally divisible
sections. Apply the singleton Koszul completion reflector to this image ideal, whose
one-element generating list follows from the image factorization. The comparison with
the strict tensor Koszul Roos complex and then the principal cone Roos complex preserves
the degree-zero unit. Transport output completeness across these comparisons. Their
unit equality identifies the reflector's invertibility criterion with the stated one. -/
theorem principalConeSmallSiteCriterion
    (a : (R.obj ⋙ forget CommRingCat).sections) (P : CochainComplex A ℤ) (μ : End P)
    (hμ : ∀ (q : ℤ) (U : Cᵒᵖ) (x : (P.X q).val.obj U),
      (μ.f q).val.app U x = @SMul.smul _ _ ((P.X q).val.obj U).isModule.toSMul (a.val U) x) :
    principalLocallyComplete.{u, u, u, w} R a
        ((DerivedCategory.Q.{w} (C := A)).obj (CochainComplex.PrincipalCone.completion μ)) ∧
      (principalLocallyComplete.{u, u, u, w} R a ((DerivedCategory.Q.{w} (C := A)).obj P) ↔
        IsIso ((DerivedCategory.Q.{w} (C := A)).map (CochainComplex.PrincipalCone.unit μ))) := by
  let := principalLocalTestSliceDerived R
  let I := image (ringedKoszulScalar R a)
  let ι := image.ι (ringedKoszulScalar R a)
  obtain ⟨D, hC, _, hcrit, _⟩ := ringedKoszulCompletionReflector R 1 (fun _ ↦ a)
    I ι (principal_generators R a)
  let b : (SheafOfModules.unit Rg).sections := ⟨a.val, a.property⟩
  obtain ⟨c, hc⟩ := principalConeKoszulRoosComparison R P a μ hμ
  obtain ⟨d, hd⟩ := principalKoszulRoos_presentation_comparison R b P D
  let e := c ≪≫ d
  have he : (DerivedCategory.Q.{w} (C := A)).map (CochainComplex.PrincipalCone.unit μ) ≫ e.hom =
      D.unit ((DerivedCategory.Q.{w} (C := A)).obj P) := by
    change _ ≫ c.hom ≫ d.hom = _
    rw [← Category.assoc, hc]
    simpa only [b] using hd
  refine ⟨(principalLocallyComplete_iff R a _).mpr
    (complete_of_iso R I ι e.symm (hC _)), ?_⟩
  rw [principalLocallyComplete_iff R a _, ← hcrit, ← he]
  exact isIso_comp_right_iff _ e.hom

end CategoryTheory
