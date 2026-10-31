/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarTensorData
/-! # The scalar tensor-data source projection -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
attribute [local irreducible] Functor.leftAdjoint Adjunction.ofIsRightAdjoint
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  _root_.DerivedCategory.Q _root_.DerivedCategory.Qh

set_option maxHeartbeats 2000000 in
-- The sealed scalar and tensor records specialize large categorical instances.
/-- Expanding the scalar tensor-data source yields the native cochain composite.
Source: finite reduction of purity, proof Step 2; Stacks 07A4 and 0FPT.
(blueprint: lem-pur-finite-scalar-source-projection).
Proof: unfold the source projection and its tensor-data record. Its three fields are
cochainLocalizationTensor, the scalar representative, and finiteTensorCochainComparison.
Their defining formulas give the displayed composite. The heterogeneous equality retains
the actual target recorded by the sealed tensor-data definition. -/
theorem finiteScalar_source_projection
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (C D : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    HEq ((finiteScalarTensorData φ T).source C D)
      ((ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).map
        (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q C D) ≫
      ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T (C ⊗ D) ≫
      _root_.DerivedCategory.Q.map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
          (ProEtale.sheafExtendScalars φ T)).app C).app D)) := by
  unfold TensorRepresentativeData.source finiteScalarTensorData
  unfold cochainLocalizationTensor finiteTensorCochainComparison
  rfl
end WeilConjectures.PurityFiniteSetting
