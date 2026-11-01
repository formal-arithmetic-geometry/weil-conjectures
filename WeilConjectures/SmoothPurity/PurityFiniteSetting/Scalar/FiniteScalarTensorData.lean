/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.TensorRepresentativeData.TensorRepresentativeData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorReductionData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarRepresentativeIso
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CochainLocalizationTensorIso
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarCochainComparisonIso

/-! # The actual scalar-extension tensor-counit diagram as typed data -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w uA vA uB vB wA wB
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The full cochain comparison diagram, with its cochain monoidal instances sealed
behind typed source and tail fields. Both arrows are the original scalar-first composites;
no witnesses or unspecified data are chosen.
Source: thm-pur-finite-reduction-of-purity, proof Step 2; Stacks 07A4 and 0FPT.
(blueprint: def-pur-finite-scalar-tensor-data). -/
@[irreducible] def finiteScalarTensorData
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    TensorRepresentativeData
      (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T)
      _root_.DerivedCategory.Q.{u + 1, u + 1, u + 2}
      _root_.DerivedCategory.Q.{u + 1, u + 1, u + 2}
      ((HomologicalComplex.quasiIso _ (.up ℤ)).kFlat) := by
  let F := (ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)
  exact
    { tensor C D := C ⊗ D
      tensor_closed X Y hC hD :=
        Eq.subst (motive := fun s => (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
            (@MonoidalCategoryStruct.tensorObj _ _ s X Y))
          (a := MonoidalCategory.toMonoidalCategoryStruct) rfl (ObjectProperty.prop_tensor hC hD)
      secondTarget C := F.obj C
      target C D := F.obj C ⊗ F.obj D
      first := cochainLocalizationTensor T
      second := ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T
      third C D := finiteTensorCochainComparison φ T C D
      tail C D :=
        (ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T C ⊗ₘ
          ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T D) ≫
        Functor.LaxMonoidal.μ _root_.DerivedCategory.Q (F.obj C) (F.obj D)
      isIso_first C D _ hD := cochainLocalizationTensor_isIso T C D hD
      isIso_second := finiteScalarRepresentative_isIso φ T
      isIso_third C D := finiteScalarCochainComparison_isIso φ T C D }

end WeilConjectures.PurityFiniteSetting
