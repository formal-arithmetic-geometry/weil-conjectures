/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
public import WeilConjectures.SixFunctors.Supporting.OperationCoefficientActionData
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompletedScalarTransportCounit

/-! # Tensor- and counit-normalized scalar transport

(blueprint: lem-pur-operation-scalar-transport-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofHasKInjectiveResolutions _root_.instCategoryDerivedCategory
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] WeilConjectures.integralCoefficientCommRingSheaf

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E F : Type u) [NormedField E] [NormedField F]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

private theorem ordinaryScalarTransport (W : Scheme.{u}) :
    ∃! e : integralOrdinaryScalar l E F i W ≅
        pbcExtend (completedCoefficientMap l E F i W),
      ∀ (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l F W).obj.obj U)
        (x : M.val.obj U),
        (e.hom.app M).val.app U (integralOrdinaryTensorSection l E F i W M U s x) =
          pbcTensorSection (completedCoefficientMap l E F i W) M U s x := by
  have hφ : integralCompletedScalarMap l E F i W = completedCoefficientMap l E F i W := by
    apply (completedCoefficientMap_existsUnique l E F i W).unique
    · exact (integralCompletedScalarMap_existsUnique l E F i W).exists.choose_spec
    · exact (completedCoefficientMap_existsUnique l E F i W).exists.choose_spec
  rw [← hφ]
  let hI : ∀ M, (integralOrdinaryScalar l E F i W).obj M =
      SheafOfModules.changeOfRings (integralCompletedScalarMap l E F i W) M :=
    (integralOrdinaryScalarWitness l E F i W).choose_spec.choose
  let hP : ∀ M, (pbcExtend (integralCompletedScalarMap l E F i W)).obj M =
      SheafOfModules.changeOfRings (integralCompletedScalarMap l E F i W) M :=
    (pbcExtensionExistence (integralCompletedScalarMap l E F i W)).choose_spec.choose
  let e : integralOrdinaryScalar l E F i W ≅
      pbcExtend (integralCompletedScalarMap l E F i W) :=
    NatIso.ofComponents (fun M ↦ eqToIso (hI M) ≪≫ (eqToIso (hP M)).symm) (by
      intro M N f
      have hIf : (integralOrdinaryScalar l E F i W).map f =
          eqToHom (hI M) ≫ SheafOfModules.changeOfRingsHom
            (integralCompletedScalarMap l E F i W) M f ≫ eqToHom (hI N).symm :=
        (integralOrdinaryScalarWitness l E F i W).choose_spec.choose_spec.choose f
      have hPf : (pbcExtend (integralCompletedScalarMap l E F i W)).map f =
          eqToHom (hP M) ≫ SheafOfModules.changeOfRingsHom
            (integralCompletedScalarMap l E F i W) M f ≫ eqToHom (hP N).symm :=
        (pbcExtensionExistence
          (integralCompletedScalarMap l E F i W)).choose_spec.choose_spec.choose f
      simp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv]
      rw [hIf, hPf]
      simp)
  have he : ∀ M U s x,
      (e.hom.app M).val.app U (integralOrdinaryTensorSection l E F i W M U s x) =
        pbcTensorSection (integralCompletedScalarMap l E F i W) M U s x := by
    intro M U s x
    have hc (z : (SheafOfModules.changeOfRings
        (integralCompletedScalarMap l E F i W) M).val.obj U) :
        (eqToHom (hI M)).val.app U ((eqToHom (hI M).symm).val.app U z) = z := by
      exact congrArg (fun f ↦ f.val.app U z)
        (show eqToHom (hI M).symm ≫ eqToHom (hI M) = 𝟙 _ by simp)
    change (eqToHom (hP M).symm).val.app U
      ((eqToHom (hI M)).val.app U ((eqToHom (hI M).symm).val.app U _)) = _
    exact congrArg (fun z ↦ (eqToHom (hP M).symm).val.app U z) (hc _)
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (cancel_epi (eqToHom (hI M).symm)).mp
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).injective
  ext1 U
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact (he' M U 1 x).trans (he M U 1 x).symm

private theorem exactScalarTransport (W : Scheme.{u}) :
    PreservesFiniteLimits (pbcExtend (completedCoefficientMap l E F i W)) ∧
      PreservesFiniteColimits (pbcExtend (completedCoefficientMap l E F i W)) := by
  let e := (ordinaryScalarTransport l E F i W).exists.choose
  exact ⟨preservesFiniteLimits_of_natIso e, preservesFiniteColimits_of_natIso e⟩

/-- Existence of the section- and universal-counit-normalized scalar transport.
Source: Stacks 03EK, 06YY; blueprint proof Steps 7 and 11
(blueprint: lem-pur-operation-scalar-transport-normalization).
Proof: the two ordinary scalar models are the same sheafified balanced tensor
construction. The identity on pure tensors gives their natural isomorphism.
Localizing on K-flat representatives gives the derived isomorphism, normalized
by the actual universal tensor counit on every complex. These are exactly the
tensor and counit fields of the recorded OperationScalarTransport interface. -/
theorem operationScalarTransport_nonempty (W : Scheme.{u}) :
    Nonempty (OperationScalarTransport l E F i W) := by
  have := (exactScalarTransport l E F i W).1
  have := (exactScalarTransport l E F i W).2
  obtain ⟨o, ho⟩ := (ordinaryScalarTransport l E F i W).exists
  obtain ⟨d, hd⟩ := derivedScalarTransport l E F i W
  refine ⟨{ ordinary := o
            tensor := ho
            derived := Functor.mapDerivedCategoryNatIso o ≪≫ d.symm
            counit := ?_ }⟩
  intro P
  change ((Functor.mapDerivedCategoryNatIso o).hom.app (DerivedCategory.Q.obj P) ≫
    d.inv.app (DerivedCategory.Q.obj P)) ≫ _ = _
  rw [← hd P, Category.assoc, ← Category.assoc (d.inv.app _), Iso.inv_hom_id_app,
    Category.id_comp]
  exact Functor.mapDerivedCategoryNatIso_fac o P

end WeilConjectures.CompactSupportCondensedRealization
