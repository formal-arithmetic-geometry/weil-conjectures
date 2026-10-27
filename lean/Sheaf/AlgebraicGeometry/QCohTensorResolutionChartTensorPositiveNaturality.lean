/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartModel
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalCoherence
import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorTransport
import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartSummandNaturality
import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionSemilinearTensor
import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionThreeSquares

/-! # Chart tensor naturality in positive degrees

The affine chart inclusion commutes with restriction and the specified semilinear maps.
Use the Sheaf chart model consistently: transport the two factors, commute the total
summand inclusion with restriction, then apply naturality of the associated-sheaf tensor map.

Source: Stacks Project, Tags 08DX(2) and 06YT.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry
attribute [local instance 2000] SheafOfModules.instCategory
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] Scheme.affineOpens ComplexShape.embeddingDownNat
  ComplexShape.Embedding.mk' Functor.mapHomologicalComplex tilde.functor
  CochainComplex.singleFunctors Functor.map₂HomologicalComplex
  TensorResolutionChartModel_localInst1 TensorResolutionSingleTensor_localInst1 affineMonoidal
attribute [local instance 2000] TensorResolutionChartModel_localInst1
  TensorResolutionChartModel_localInst2 TensorResolutionChartModel_localInst3
  TensorResolutionChartModel_localInst4
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] tensorResolutionChartModel tensorResolutionRestrictionTensorMap
  tensorResolutionSemilinearMap tensorResolutionTildeTensorHom
set_option maxHeartbeats 800000 in
-- Tensor-resolution comparisons require substantial definitional reduction.
/-- Naturality of the chart tensor inclusion after transport to nonzero degrees. -/
theorem tensorResolutionChartTensorIso_naturality_positive_core {Y : Scheme.{u}}
    (N : Y.Modules) [N.IsQuasicoherent]
    (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (MB NB : ModuleCat.{u} (Γ(Y, V.1) : Type u))
    (sA : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (sB : NB ≃ₗ[Γ(Y, V.1)] N.val.obj (op V.1))
    (PA : ProjectiveResolution MA) (PB : ProjectiveResolution MB) :
    let φ := Y.presheaf.map (homOfLE h).op
    let R := Scheme.Modules.restrictFunctor (Spec.map φ)
    let _RC := R.mapHomologicalComplex (.up ℤ)
    let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let RV := (Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let LA := ((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj PA.complex
    let LB := ((tensorRight NB).mapHomologicalComplex (.down ℕ)).obj PB.complex
    let EA := tensorResolutionChartComplex U MA PA
    let EB := tensorResolutionChartComplex V MB PB
    let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
    ∀ (b : NA ⟶ (ModuleCat.restrictScalars φ.hom).obj NB)
      (a : PA.complex ⟶ ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex (.down
        ℕ)).obj PB.complex)
      (k : LA ⟶ ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex (.down ℕ)).obj LB),
      (∀ y, sB (b y) = N.val.map (homOfLE h).op (sA y)) →
      (∀ (j : ℕ) (x : PA.complex.X j) (y : NA),
        k.f j (x ⊗ₜ[Γ(Y, U.1)] y) =
          (show PB.complex.X j from a.f j x) ⊗ₜ[Γ(Y, V.1)] (show NB from b y)) →
      let a' := tensorResolutionSemilinearComplexMap φ (.up ℤ)
        (PA.complex.extend ComplexShape.embeddingDownNat) (PB.complex.extend
          ComplexShape.embeddingDownNat)
        (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat PA.complex
          PB.complex a)
      let _k' := tensorResolutionSemilinearComplexMap φ (.up ℤ)
        (LA.extend ComplexShape.embeddingDownNat) (LB.extend ComplexShape.embeddingDownNat)
        (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat LA LB k)
      ∀ j : ℕ,
      let i := -(j : ℤ)
      let fA := tilde.map
        (PA.complex.extendXIso ComplexShape.embeddingDownNat (i := j) (i' := i) rfl).inv
      let fB := tilde.map
        (PB.complex.extendXIso ComplexShape.embeddingDownNat (i := j) (i' := i) rfl).inv
      let gA := (tensorResolutionChartModel N U NA sA).hom ≫
        (Scheme.Modules.restrictFunctor U.2.fromSpec).map
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv
      let gB := (tensorResolutionChartModel N V NB sB).hom ≫
        (Scheme.Modules.restrictFunctor V.2.fromSpec).map
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv
      R.map (tensorResolutionTildeTensorHom _ (PA.complex.X j) NA) ≫
        R.map (fA ⊗ₘ gA) ≫
          R.map (HomologicalComplex.ιMapBifunctor EA (RU.obj N0) (curriedTensor _)
            (.up ℤ) i 0 i (by simp)) ≫
          (tensorResolutionRestrictionTensorMap (Spec.map φ)
            EA (RU.obj N0) EB (RV.obj N0) a'
            (tensorResolutionChartRestrictionComplexIso Y V U h N0).hom).f i =
        tensorResolutionSemilinearMap φ (k.f j) ≫
          tensorResolutionTildeTensorHom _ (PB.complex.X j) NB ≫
          (fB ⊗ₘ gB) ≫
          HomologicalComplex.ιMapBifunctor EB (RV.obj N0) (curriedTensor _)
            (.up ℤ) i 0 i (by simp) := by
  intro φ R RC RU RV LA LB EA EB N0 b a k hb hk a' k' j i fA fB gA gB
  have hs := tensorResolutionChartSummand_naturality N V U h MA NA MB NB sA sB PA PB a j
  have hf := tensorResolutionChartTensor_transport N V U h MA NA MB NB sA sB PA PB b a hb j
  have ht := tensorResolutionSemilinearMap_tensor (Y.presheaf.map (homOfLE h).op)
    (PA.complex.X j) NA (PB.complex.X j) NB (a.f j) b (k.f j) (hk j)
  have hc := tensorResolution_three_squares _ _ _ _ _ _ _ _ _ _ _ _ hs hf ht
  exact hc
end AlgebraicGeometry
