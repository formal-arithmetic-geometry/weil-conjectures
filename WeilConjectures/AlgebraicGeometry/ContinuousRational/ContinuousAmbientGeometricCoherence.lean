/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalRealizationData
import WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationScalarCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalAdjunctionUnit

/-! # Normalized continuous tensor coherence

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15
(blueprint: lem-per-continuous-ambient-geometric-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.ContinuousRational

attribute [local irreducible] HasDerivedCategory.standard
  Functor.sheafPullbackConstruction.sheafPullback proEtaleRingInverseImageComp
  LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem tensor_transport (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : pbcModules X R) (W : X.ProEtᵒᵖ) (s : R.obj.obj W) (m : M.val.obj W) :
    (eqToHom ((completedAdicChangeData X (𝟙 R)).choose_spec.choose M)).val.app W
        (pbcTensorSection (𝟙 R) M W s m) =
      (toSheafify (ProEt.topology X)
        (SheafOfModules.changeOfRingsPresheaf (𝟙 R) M).presheaf).app W
          (s ⊗ₜ[R.obj.obj W, ((𝟙 R : R ⟶ R).hom.app W).hom] m) := by
  simp only [pbcTensorSection, completedAdicChangeTensor, ← ConcreteCategory.comp_apply,
    ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val, eqToHom_trans,
    eqToHom_refl, SheafOfModules.id_val, PresheafOfModules.id_app,
    ConcreteCategory.id_apply]

attribute [-instance] coefficientProEtaleModelBaseChange_isContinuous
  coefficientProEtaleModelUp_isContinuous in
end AlgebraicGeometry.Scheme.ContinuousRational
