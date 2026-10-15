/- Copyright (c) 2026. All rights reserved. -/
module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionHomologyCoherence
import Sheaf.Algebra.Homology.KFlat
import Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # K-flat chart comparison naturality

Source: Stacks Project, Tags 08DX(2), 06YT and 01I9.
(blueprint: new-t3-qcoh-tensor-resolution-chart-comparison-naturality).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance QCohTensorResolutionChartComparisonNaturality_monoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance QCohTensorResolutionChartComparisonNaturality_zero
    (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance QCohTensorResolutionChartComparisonNaturality_objZero
    (X : Scheme.{u}) (L : X.Modules) :
    ((curriedTensor X.Modules).obj L).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf L

/-- Naturality of the common K-flat comparison and normalized open restriction.

Source: Stacks Tags 08DX(2), 06YT and 01I9: compare the two ordinary tensor
calculations through a common K-flat resolution and use functorial restriction.

Proof in words: the formula ha implies that the extended sheafification of a
commutes with the two chart augmentations to M[0]; this is exactly
 tensorResolutionChartAugmentation_naturality. The restriction complex isomorphisms
for K, F, M[0] and N[0] commute with q and s by naturality. Apply
 tensorResolution_restrictedTensor_square to these squares and the augmentation
square. This gives the four commuting squares between the legs of the tensor
zigzags through the same restricted F. Take homology, inserting the inverse
exact-restriction homology isomorphism at each vertex. Every horizontal leg of
the zigzag is invertible by K-flat tensor invariance. The elementary cancellation
lemma tensorResolution_homology_zigzag therefore gives the comparison square.
The normalized open-restriction homology isomorphism is itself natural by
 tensorResolutionNormalizedRestrictHomologyIso_naturality, using the total tensor
restriction square tensorResolutionChartRestriction_total. Compose its inverse
square with the comparison square and cancel adjacent inverse isomorphisms to
obtain the displayed formula. Neither b, k nor a coefficient presentation of N
is involved. The argument allows arbitrary n, zero complexes and unbounded K.

(blueprint: new-t3-qcoh-tensor-resolution-chart-comparison-naturality) -/
theorem tensorResolutionChartComparisonIso_naturality
    (Y : Scheme.{u}) (M N : Y.Modules) [M.IsQuasicoherent]
    (MA : ∀ U : Y.affineOpens, ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : ∀ U : Y.affineOpens, MA U ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (P : ∀ U, ProjectiveResolution (MA U))
    (K F : CochainComplex Y.Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj M)
    (s : F ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj N)
    (hK : CochainComplex.IsKFlat (R := Y.sheaf) K)
    (hF : CochainComplex.IsKFlat (R := Y.sheaf) F)
    (hq : QuasiIso q) (hs : QuasiIso s) (n : ℕ)
    (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (a : (P U).complex ⟶ ((ModuleCat.restrictScalars
      (Y.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex (.down ℕ)).obj
        (P V).complex)
    (ha : ∀ x : (P U).complex.X 0,
      sM V ((P V).π.f 0 (a.f 0 x)) =
        M.val.map (homOfLE h).op (sM U ((P U).π.f 0 x))) :
    let φ := Y.presheaf.map (homOfLE h).op
    let R := Scheme.Modules.restrictFunctor (Spec.map φ)
    let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
    let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let RV := (Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let EA := tensorResolutionChartComplex U (MA U) (P U)
    let EB := tensorResolutionChartComplex V (MA V) (P V)
    let α := tensorResolutionSemilinearComplexMap φ (.up ℤ)
      ((P U).complex.extend ComplexShape.embeddingDownNat)
      ((P V).complex.extend ComplexShape.embeddingDownNat)
      (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat
        (P U).complex (P V).complex a)
    let β := tensorResolutionRestrictionTensorMap (Spec.map φ) EA (RU.obj N0)
      EB (RV.obj N0) α (tensorResolutionChartRestrictionComplexIso Y V U h N0).hom
    R.map (tensorResolutionChartComparisonIso Y M N U (MA U) (sM U) (P U)
        K F q s hK hF hq hs (-(n : ℤ)) ≪≫
      (tensorResolutionNormalizedRestrictHomologyIso U.2.fromSpec K N0 (-(n : ℤ))).symm).hom ≫
      (tensorResolutionChartRestrictionIso Y V U h).hom.app
        ((CochainComplex.mapBifunctor K N0 (curriedTensor Y.Modules)).homology (-(n : ℤ))) =
    (((CochainComplex.mapBifunctor EA (RU.obj N0)
        (curriedTensor (Spec Γ(Y, U.1)).Modules)).sc (-(n : ℤ))).mapHomologyIso R).inv ≫
      HomologicalComplex.homologyMap β (-(n : ℤ)) ≫
        (tensorResolutionChartComparisonIso Y M N V (MA V) (sM V) (P V)
            K F q s hK hF hq hs (-(n : ℤ)) ≪≫
          (tensorResolutionNormalizedRestrictHomologyIso V.2.fromSpec K N0 (-(n : ℤ))).symm).hom
    := by
  sorry

end AlgebraicGeometry
