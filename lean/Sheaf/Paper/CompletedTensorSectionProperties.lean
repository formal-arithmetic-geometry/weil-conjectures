/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R6
-/
module

public import Sheaf.Paper.FiniteFreeCompletedScalarComparison

/-! # Unit-tensor naturality in the completed ordinary scalar model

The actual sheafified tensor construction respects completed scalar multiplication
and restriction of unit tensors (blueprint: lem-weil-completed-tensor-section-properties).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
open scoped ChangeOfRings
namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedScalarChangeData completedScalarTensorSection
attribute [local implicit_reducible] completedOrdinaryScalarExtension

private theorem tensorSection_smul (W : AlgebraicGeometry.Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (A : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
    (U : W.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)) =
      a • ((eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) := by
  subst A
  let k := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M)).app U ≫
      (ModuleCat.restrictScalarsId (S.obj.obj U)).hom.app _
  change k (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) =
    a • k ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)
  have ht : a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x =
      a • ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) := by
    change a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x =
      (a * 1) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x
    rw [mul_one]
  rw [ht]
  exact k.hom.map_smul a _


private theorem tensorSection_restrict (W : AlgebraicGeometry.Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (A : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
    {U V : W.ProEtᵒᵖ} (f : U ⟶ V) (x : M.val.obj U) :
    A.val.map f ((eqToHom hA.symm).val.app U
      ((toSheafify (ProEt.topology W)
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) =
      (eqToHom hA.symm).val.app V
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app V
            ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V,(φ.hom.app V).hom] M.val.map f x)) := by
  subst A
  let N := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)).unit.app N
  have hη := (PresheafOfModules.naturality_apply η f
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)).symm
  change (SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M).val.map f
      ((toSheafify (ProEt.topology W) N.presheaf).app U
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)) =
    (toSheafify (ProEt.topology W) N.presheaf).app V
      (N.map f ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)) at hη
  refine hη.trans ?_
  change (toSheafify (ProEt.topology W) N.presheaf).app V
      (N.map f ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)) =
    (toSheafify (ProEt.topology W) N.presheaf).app V
      ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V,(φ.hom.app V).hom] M.val.map f x)
  exact congrArg ((toSheafify (ProEt.topology W) N.presheaf).app V)
    ((Classical.choose_spec
      (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1} φ M f) 1 x).trans
        (by rw [map_one]))

/-- Linearity and restriction naturality for the actual completed tensor sections.
Source: Stacks Project, Modules on Sites, Section 03EK.
(blueprint: lem-weil-completed-tensor-section-properties).
Proof: transport to the sheafified extension-of-scalars object. Its sheafification
unit is linear, so a tensor x equals a times the unit tensor x. Naturality of that
unit sends a restricted unit tensor to the unit tensor of the restricted section,
since the coefficient restriction preserves one. Transport back along the object
equality, whose induced sheaf morphism is linear and natural. -/
theorem completedTensorSectionProperties
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (W : AlgebraicGeometry.Scheme.{u})
    (M : integralTowerModules l E W) :
    (∀ (U : W.ProEtᵒᵖ)
      (a : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
      (x : M.val.obj U),
      completedScalarTensorSection l E L ι W M U a x =
        a • completedScalarTensorSection l E L ι W M U 1 x) ∧
    (∀ {U V : W.ProEtᵒᵖ} (f : U ⟶ V) (x : M.val.obj U),
      (((completedOrdinaryScalarExtension l E L ι W).obj M).val.map f)
          (completedScalarTensorSection l E L ι W M U 1 x) =
        completedScalarTensorSection l E L ι W M V 1 (M.val.map f x)) := by
  constructor
  · intro U a x
    unfold completedScalarTensorSection
    exact tensorSection_smul W (completedCoefficientMap l E L ι W) M _
      ((completedScalarChangeData l E L ι W).choose_spec.choose M) U a x
  · intro U V f x
    unfold completedScalarTensorSection
    exact tensorSection_restrict W (completedCoefficientMap l E L ι W) M _
      ((completedScalarChangeData l E L ι W).choose_spec.choose M) f x

end WeilConjectures
