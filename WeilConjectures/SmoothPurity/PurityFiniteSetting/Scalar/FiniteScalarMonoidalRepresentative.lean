/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarMonoidalModel
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarTensorData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarNativeTensorComparisonTransport
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarNativeTensorComparisonCounit
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarSourceProjection
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarModelProjection

/-! # The representative equation for constructed scalar monoidal transport

Source: finite reduction of purity, proof Step 2; Stacks 07A4 and 0FPT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Functor.leftAdjoint Adjunction.ofIsRightAdjoint
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  _root_.DerivedCategory.Q _root_.DerivedCategory.Qh

private theorem finiteScalar_transfer_tensor_counit
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F G : C ⥤ D) (e : F ≅ G)
    {P Q T : C} {EP EQ V : D} (t : P ⊗ Q ⟶ T) (t' : EP ⊗ EQ ⟶ V)
    (εP : G.obj P ⟶ EP) (εQ : G.obj Q ⟶ EQ) (εT : G.obj T ⟶ V)
    (τ : G.obj (P ⊗ Q) ⟶ G.obj P ⊗ G.obj Q)
    (h : G.map t ≫ εT = τ ≫ (εP ⊗ₘ εQ) ≫ t') :
    F.map t ≫ (e.hom.app T ≫ εT) =
      (e.hom.app (P ⊗ Q) ≫ τ ≫ (e.inv.app P ⊗ₘ e.inv.app Q)) ≫
        ((e.hom.app P ≫ εP) ⊗ₘ (e.hom.app Q ≫ εQ)) ≫ t' := by
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc,
    Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% e.hom.naturality, h]

set_option maxHeartbeats 2000000 in
-- The sealed categorical record expansion needs a larger heartbeat budget.
/-- Expanding the tensor-data and monoidal-model records turns the representative
right hand side into the native cochain counit square. -/
private theorem finiteScalarRepresentative_target_of_native
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (C D : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    letI : Algebra A B := φ.toAlgebra
    letI : (ProEtale.sheafExtendScalars φ T).PreservesKFlatQuasiIso :=
      ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B T
    letI : (ProEtale.sheafExtendScalars φ T).leftDerivedFunctor.Monoidal :=
      (ProEtale.sheafExtendScalars φ T).leftDerivedFunctorMonoidal
    let e := finiteScalarDerivedComparison φ T
    ∀ (_h : (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).map
      (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q C D) ≫
        ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T (C ⊗ D) ≫
          _root_.DerivedCategory.Q.map
            (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
              (ProEtale.sheafExtendScalars φ T)).app C).app D) =
      e.hom.app (_root_.DerivedCategory.Q.obj C ⊗ _root_.DerivedCategory.Q.obj D) ≫
        ((ProEtale.sheafExtendScalars φ T).leftDerivedTensorComparison.app
          (_root_.DerivedCategory.Q.obj C)).app (_root_.DerivedCategory.Q.obj D) ≫
        ((e.inv.app (_root_.DerivedCategory.Q.obj C) ≫
          ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T C) ⊗ₘ
        (e.inv.app (_root_.DerivedCategory.Q.obj D) ≫
          ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T D)) ≫
        Functor.LaxMonoidal.μ _root_.DerivedCategory.Q
          (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj C)
          (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj D)),
    (finiteScalarTensorData φ T).source C D =
      ((finiteScalarMonoidalModel φ T).μIso
        (_root_.DerivedCategory.Q.obj C) (_root_.DerivedCategory.Q.obj D)).inv ≫
          (finiteScalarTensorData φ T).tail C D := by
  dsimp only
  intro h
  exact eq_of_heq ((finiteScalar_source_projection φ T C D).trans
    ((heq_of_eq h).trans (finiteScalar_model_projection φ T C D).symm))

set_option maxHeartbeats 2000000 in
-- Expanding the typed scalar diagram specializes large derived-category instances.
/-- The explicitly transported native tensorator satisfies the full cochain counit square.
Source: thm-pur-finite-reduction-of-purity, proof Step 2; Stacks 07A4 and 0FPT.
(blueprint: lem-pur-finite-scalar-monoidal-representative).

Proof: the native left-derived tensor comparison is characterized by its counit
square on the homotopy category. Pass from homotopy objects to cochain objects
using quotientCompQhIso and the quotient functor's monoidal structure. The exact
restriction comparison mapDerivedCategoryFactors identifies the transpose of the
localized ordinary scalar unit with that same derived counit. Uniqueness of left
adjoints identifies this transpose for the chosen fixed scalar adjunction with
the native counit preceded by the inverse leftAdjointUniq comparison. Substitute
this identity in each of the three counit components. The formula for monoidal
transport cancels the two tensor factors of leftAdjointUniq and its tensor-source
component. What remains is exactly the native tensor comparison's counit square.
This argument is natural for every pair of complexes; it does not require the
coefficient morphism to be flat or the complexes to be bounded or K-flat. It also
applies to the identity coefficient morphism, zero rings and the empty scheme. -/
theorem finiteScalarMonoidalModel_representative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (C D : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    (finiteScalarTensorData φ T).source C D =
      ((finiteScalarMonoidalModel φ T).μIso
        (_root_.DerivedCategory.Q.obj C) (_root_.DerivedCategory.Q.obj D)).inv ≫
          (finiteScalarTensorData φ T).tail C D := by
  let : Algebra A B := φ.toAlgebra
  let : (ProEtale.sheafExtendScalars φ T).PreservesKFlatQuasiIso :=
    ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B T
  let : (ProEtale.sheafExtendScalars φ T).leftDerivedFunctor.Monoidal :=
    (ProEtale.sheafExtendScalars φ T).leftDerivedFunctorMonoidal
  let e := finiteScalarDerivedComparison φ T
  have hr := finiteScalarRepresentative_comparison φ T
  have hn := finiteScalarNativeTensorComparison_counit φ T C D
  have ht := finiteScalar_transfer_tensor_counit
    (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T)
    (ProEtale.sheafExtendScalars φ T).leftDerivedFunctor e
    (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q C D)
    (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q
      (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj C)
      (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj D))
    ((ProEtale.sheafExtendScalars φ T).rightExact_cochainCounit C)
    ((ProEtale.sheafExtendScalars φ T).rightExact_cochainCounit D)
    ((ProEtale.sheafExtendScalars φ T).rightExact_cochainCounit (C ⊗ D) ≫
      _root_.DerivedCategory.Q.map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
          (ProEtale.sheafExtendScalars φ T)).app C).app D))
    (((ProEtale.sheafExtendScalars φ T).leftDerivedTensorComparison.app
      (_root_.DerivedCategory.Q.obj C)).app
      (_root_.DerivedCategory.Q.obj D)) hn
  have hrT := congrArg (fun z ↦ z ≫ _root_.DerivedCategory.Q.map
    (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
      (ProEtale.sheafExtendScalars φ T)).app C).app D))
    (hr (C ⊗ D))
  simp only [Category.assoc] at hrT ht
  rw [← hrT] at ht
  rw [← hr C, ← hr D] at ht
  rw [tensorHom_comp_tensorHom_assoc] at ht
  exact finiteScalarRepresentative_target_of_native φ T C D ht

end WeilConjectures.PurityFiniteSetting
