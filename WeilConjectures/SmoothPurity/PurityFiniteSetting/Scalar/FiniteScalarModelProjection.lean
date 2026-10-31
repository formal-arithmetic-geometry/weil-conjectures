/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarMonoidalModel
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarTensorData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarDerivedComparison
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarModelTensorator
/-! # The scalar monoidal-model target projection -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
attribute [local irreducible] Functor.leftAdjoint Adjunction.ofIsRightAdjoint
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  _root_.DerivedCategory.Q _root_.DerivedCategory.Qh
  Functor.leftDerivedFunctorMonoidal Functor.leftDerivedFunctorOplaxMonoidal
  Functor.Monoidal.coreMonoidalTransport Adjunction.leftAdjointUniq

set_option maxHeartbeats 2000000 in
-- The target is kept heterogeneous while expanding the tensor-data tail.
private theorem data_tail
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (C D : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    HEq ((finiteScalarTensorData φ T).tail C D)
      ((ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T C ⊗ₘ
        ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T D) ≫
      Functor.LaxMonoidal.μ _root_.DerivedCategory.Q
        (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj C)
        (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj D)) := by
  unfold finiteScalarTensorData
  rfl

set_option maxHeartbeats 2000000 in
-- Identify objects before composing heterogeneous arrows.
private theorem data_target
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (C D : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    (finiteScalarTensorData φ T).obj C D =
      _root_.DerivedCategory.Q.obj
        ((((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj C) ⊗
          (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj D)) := by
  unfold TensorRepresentativeData.obj finiteScalarTensorData
  rfl

set_option maxHeartbeats 2000000 in
-- The sealed scalar and tensor records specialize large categorical instances.
/-- Expanding the transported model and its recorded tail gives the native composite.
Source: finite reduction of purity, proof Step 2; Stacks 07A4 and 0FPT.
(blueprint: lem-pur-finite-scalar-model-projection).
Proof: expand coreMonoidalTransport_μIso_inv and identify the native inverse tensorator
with leftDerivedTensorComparison. Expand the tensor-data tail and distribute tensorHom
across composition. The inverse leftAdjointUniq comparison is finiteScalarDerivedComparison.
Heterogeneous equality retains the sealed record target without eliminating its Shrink. -/
theorem finiteScalar_model_projection
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (C D : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    letI : Algebra A B := φ.toAlgebra
    letI : (ProEtale.sheafExtendScalars φ T).PreservesKFlatQuasiIso :=
      ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B T
    letI : (ProEtale.sheafExtendScalars φ T).leftDerivedFunctor.Monoidal :=
      (ProEtale.sheafExtendScalars φ T).leftDerivedFunctorMonoidal
    let e := finiteScalarDerivedComparison φ T
    HEq
      (((finiteScalarMonoidalModel φ T).μIso
        (_root_.DerivedCategory.Q.obj C) (_root_.DerivedCategory.Q.obj D)).inv ≫
        (finiteScalarTensorData φ T).tail C D)
      ((e.hom.app (_root_.DerivedCategory.Q.obj C ⊗ _root_.DerivedCategory.Q.obj D) ≫
      ((ProEtale.sheafExtendScalars φ T).leftDerivedTensorComparison.app
        (_root_.DerivedCategory.Q.obj C)).app (_root_.DerivedCategory.Q.obj D) ≫
      ((e.inv.app (_root_.DerivedCategory.Q.obj C) ≫
        ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T C) ⊗ₘ
      (e.inv.app (_root_.DerivedCategory.Q.obj D) ≫
        ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T D)) ≫
      Functor.LaxMonoidal.μ _root_.DerivedCategory.Q
        (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj C)
        (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj D))) := by
  dsimp only
  refine (heq_comp rfl rfl (data_target φ T C D)
    (finiteScalar_model_tensorator φ T (_root_.DerivedCategory.Q.obj C)
      (_root_.DerivedCategory.Q.obj D)) (data_tail φ T C D)).trans ?_
  apply heq_of_eq
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc]

end WeilConjectures.PurityFiniteSetting
