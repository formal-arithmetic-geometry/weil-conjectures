/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumCoefficientComputation
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartSumKFlat
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartProperModelScalar
import all WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumCoefficientComputation
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleCompactificationBoundedModels
import all WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility

/-! # Scalar compatibility at the graph boundary on flat K-flat representatives

Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-sum-boundary-scalar).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar

/-- Scalar compatibility at the graph boundary on flat K-flat representatives.
Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-sum-boundary-scalar).

Proof: The graph comparison is a componentwise isomorphism. Native K-flatness of the summed
complex transfers along it to the compactified direct-image complex.
Apply the proper coefficient model equation with this direct-image K-flatness. Termwise flatness
and native K-flatness supply the exact open-tensor representative normalization.
Use naturality of the proper coefficient map, scalar representative and acyclic comparison. Paste
these squares with the complex graph coefficient equation, and identify the open coefficient
comparison with its normalized tensor isomorphism. -/
theorem ordinaryChartSumBoundaryScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [IsNoetherian U] [IsNoetherian V] (c : Compactification e)
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hf : ∀ n, ObjectProperty.flat (P.X n)) :
    (scalarExtension φ V).map (etaleSumCompactifiedModelBoundary A e c P) ≫
        (properCoefficientMap φ c.g).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
            (DerivedCategory.Q.obj P)) ≫
        (rightDerivedLowerStar (ModuleCat.{u + 1} B) c.g).map
          (properOpenCoefficientOpenIso φ c.i (DerivedCategory.Q.obj P)).hom ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
          (scalarExtensionRepresentative φ U P) =
      scalarExtensionRepresentative φ V
          (((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (etaleSumScalarComplexMap φ e P) ≫
        etaleSumCompactifiedModelBoundary B e c (coefficientExtendedComplex φ U P) := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have := compactification_graph_isIso A e c
  have (n : ℤ) : IsIso ((etaleSumCompactifiedComplexMap A e c P).f n) := by
    unfold etaleSumCompactifiedComplexMap
    change IsIso ((etaleCompactificationGraphMap A e c).app (P.X n))
    infer_instance
  have : IsIso (etaleSumCompactifiedComplexMap A e c P) :=
    HomologicalComplex.Hom.isIso_of_components _
  have hDV : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (compactifiedEtaleDirectComplex A c P) :=
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat.prop_of_iso
      (asIso (etaleSumCompactifiedComplexMap A e c P))
      (ordinaryChartSumKFlat A e P hP)
  have hproper := ordinaryChartProperModelScalar c.g φ
    (compactifiedEtaleOpenComplex A c P) hDV
  let δA :=
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryFactors.inv.app P
  let o := complexCompositeMap
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
    (ProEtale.etaleSheafExtendScalars φ c.Z)
    (ProEtale.etaleSheafExtendScalars φ U)
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i)
    (openScalarExtensionZero φ c.i).hom P
  have hn := (properCoefficientMap φ c.g).naturality δA
  have ho := (etaleOpenTensorComparisons φ c.i).q_normalized P
    (etaleKFlat_of_flat_native A U P hP hf)
  have hs := (scalarRepresentativeTransformation φ V).naturality
    (etaleSumCompactifiedComplexMap A e c P)
  simp only [scalarRepresentativeTransformation_app, complexLocalization,
    Functor.comp_map] at hs
  have ha := acyclicComparison_naturality B c.g
    (C := coefficientExtendedComplex φ c.Z (compactifiedEtaleOpenComplex A c P))
    (C' := compactifiedEtaleOpenComplex B c (coefficientExtendedComplex φ U P)) o
  have ho_eq : o =
      (Functor.mapHomologicalComplexCompIso (openScalarExtensionZero φ c.i)
        (.up ℤ)).hom.app P := complexCompositeMap_iso _ _ _ _ _ _
  rw [ho_eq] at ha
  have hg := congrArg DerivedCategory.Q.map (scalar_graph_complex φ e c P)
  simp only [Functor.map_comp] at hg
  dsimp only [derivedExtension] at ho
  dsimp only [properCoefficientTensor] at hproper
  have hRo := congrArg (rightDerivedLowerStar (ModuleCat.{u + 1} B) c.g).map ho
  simp only [Functor.map_comp] at hRo
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [rightDerivedLowerStar, Functor.comp_obj, Functor.comp_map] at hn hRo hproper ha
  have hd := paste_coefficient_squares hn hRo
    (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      dsimp only [δA]
      rw [Iso.inv_hom_id_app]
      dsimp only [Functor.comp_obj]
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id])
    (by
      rw [← Functor.map_comp, Iso.hom_inv_id_app]
      dsimp only [Functor.comp_obj]
      rw [CategoryTheory.Functor.map_id])
    hproper ha hs hg
  rw [open_scalar_iso_eq]
  simpa only [etaleSumCompactifiedModelBoundary,
    rightDerivedLowerShriekOfCompactification, rightDerivedLowerStar,
    Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc,
    δA, coefficientExtendedComplex, compactifiedEtaleOpenComplex] using hd

end AlgebraicGeometry.Etale
