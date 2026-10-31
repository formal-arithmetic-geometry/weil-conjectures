/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarDerivedComparison
public import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedAdjointCochainCounit

/-! # The fixed scalar representative and the native derived counit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Functor.leftAdjoint Adjunction.ofIsRightAdjoint
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit

private theorem cochainAdjunction_unit
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (E : A ⥤ B) (U : B ⥤ A) [E.Additive] [U.Additive] (adj : E ⊣ U)
    (C : CochainComplex A ℤ) :
    (adj.mapHomologicalComplex (.up ℤ)).unit.app C =
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app C ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app C ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app C := by
  ext i : 1
  simp only [Functor.id_obj, Functor.comp_obj, Adjunction.mapHomologicalComplex_unit_app_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexIdIso_inv_app_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv, NatTrans.id_app]
  exact ((Category.id_comp (adj.unit.app (C.X i) ≫ 𝟙 ((E ⋙ U).obj (C.X i)))).trans
    (Category.comp_id (adj.unit.app (C.X i)))).symm

/-- The fixed-adjunction scalar representative is the native derived counit preceded
by the canonical left-adjoint comparison. Source: Stacks 06YY and 07A4.
(blueprint: lem-pur-finite-scalar-native-tensor-comparison-transport).
Proof: the ordinary mapped cochain unit is the unit of the induced cochain adjunction,
as checked degreewise. The derived-adjunction cochain counit theorem identifies its
transpose under the fixed adjunction. The inverse of leftAdjointUniq is the comparison
for the two adjunctions in opposite order, so this is the stated comparison. -/
theorem finiteScalarRepresentative_comparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (C : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    letI : Algebra A B := φ.toAlgebra
    let F := ProEtale.sheafExtendScalars φ T
    letI : F.PreservesKFlatQuasiIso :=
      ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B T
    ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T C =
      (finiteScalarDerivedComparison φ T).hom.app (_root_.DerivedCategory.Q.obj C) ≫
        F.rightExact_cochainCounit C := by
  let : Algebra A B := φ.toAlgebra
  let E := ProEtale.sheafExtendScalars φ T
  let U := Sheaf.restrictScalars (Scheme.ProEt.topology T) φ
  let : E.PreservesKFlatQuasiIso :=
    ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B T
  let adj := ProEtale.sheafExtendScalarsAdjunction φ T
  let ad := Adjunction.ofIsRightAdjoint
    (ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T)
  let : PreservesFiniteLimits U := by
    let := adj.rightAdjoint_preservesLimits
    infer_instance
  let : PreservesFiniteColimits U := by
    let r := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) φ
    let := r.leftAdjoint_preservesColimits
    infer_instance
  have h := (Adjunction.leftDerivedCochainCounit E U adj ad C).symm
  rw [cochainAdjunction_unit E U adj C] at h
  have hab : ProEtale.leftDerivedSheafExtendScalarsAdjunction A B T =
      adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory := by
    simp only [ProEtale.leftDerivedSheafExtendScalarsAdjunction,
      RingHom.algebraMap_toAlgebra, adj, U]
  rw [← hab] at h
  simpa only [ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative,
    finiteScalarDerivedComparison, Functor.rightExact_cochainCounit,
    Adjunction.leftAdjointUniq_inv_app, E, U, adj, ad, Functor.id_obj,
    ProEtale.SupportedEtaleTensorOrigin.proFixedScalar, ProEtale.pbcFixedScalarExtension,
    Iso.symm_hom, Iso.app_inv, Iso.app_hom, Category.assoc] using h

end WeilConjectures.PurityFiniteSetting
