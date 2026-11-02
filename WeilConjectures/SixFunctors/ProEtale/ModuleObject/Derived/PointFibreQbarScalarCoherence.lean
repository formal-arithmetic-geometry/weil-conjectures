/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointTensorReduction.CondensedPointTensorReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointFibreTensorModels
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExactScalarPointCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.CategoryTheory.ZetaWeil.SectionRingGlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
public import WeilConjectures.CategoryTheory.Preadditive.CoyonedaSectionsExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.CommonFieldLatticeGenerators
import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfect
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeModulePullbackBraiding
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationUnderivedModel
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ZetaWeil.ContractibleLisseEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectRingClassicalGenerator
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Subcategory
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.FinitePointComparison.CondensedPointDerivedScalarComparison
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree

/-! # Rational point-fibre scalar coherence

Source: latest blueprint, `sk-thm-sf-kunneth-relative`, finite-reduction and
scalar-extension clause, specialized to the geometric point; DAG proof Steps 1--4
(blueprint: lem-sf-point-fibre-qbar-scalar-coherence).

The native cup is transported through evaluation at 1 and the canonical singleton
scalar-ring isomorphism. Identity, composition and passage to the algebraic closure
are equations on the ambient fibre/change comparisons, with balanced-tensor
normalizations for the ordinary derived unitors and compositors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.PointTensorReduction
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct ChangeOfRings

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The bundled finite-subextension inclusion used by the qbar scalar package.
Source: coefficient inclusions, proof Step 2
(blueprint: lem-sf-point-fibre-qbar-scalar-coherence). -/
noncomputable def qbarFieldMap (ell : ℕ) [Fact ell.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
    scalarSixFieldRing.{u} ell E ⟶ scalarSixFieldRing ell F :=
  ⟨⟨Profinite.padicSubfieldRingObjMap ell h⟩⟩

/-- The bundled inclusion of a finite subextension into the algebraic-closure coefficient.
Source: coefficient inclusions, proof Step 2
(blueprint: lem-sf-point-fibre-qbar-scalar-coherence). -/
noncomputable def qbarClosureMap (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    scalarSixFieldRing.{u} ell E ⟶ latticeClosureRing ell :=
  ⟨⟨Profinite.padicSubfieldRingObjToPadicAlgCl ell E⟩⟩

/-- Restrict regular-module scalars through the canonical singleton-section isomorphism.
Source: geometric-point evaluation, proof Step 1
(blueprint: lem-sf-point-fibre-qbar-scalar-coherence). -/
abbrev qbarNativeRestriction (Λ : ScalarSixRing.{u}) :
    ModuleCat.{u + 1} (MonObj.Γ Λ.X) ⥤ ModuleCat.{u + 1} (condensedScalarRing Λ.X) :=
  ModuleCat.restrictScalars.{u + 1}
    (InternalAbelianSheafModule.sectionGlobalEquiv
      (coherentTopology Profinite.{u}) Λ.X (⊤_ Profinite.{u}) terminalIsTerminal).symm.toRingHom

/-- The exact/right-derived transport associated to an ordinary section identification.
Source: geometric-point evaluation, proof Step 1
(blueprint: lem-sf-point-fibre-qbar-scalar-coherence). -/
def qbarNativeFiberIso (Λ : ScalarSixRing.{u}) (k : Type u) [Field k] [IsAlgClosed k]
    (q : condensedRingCoefficientSections Λ.X (Spec (.of k)) ⋙ qbarNativeRestriction Λ ≅
      CohomologyTransport.sections Λ.X (Spec (.of k))) :
    TraceCupPoint.fiber Λ.X k ⋙ (qbarNativeRestriction Λ).mapDerivedCategory ≅ fiber Λ k :=
  Functor.isoWhiskerRight (TraceCupPoint.exactComparison Λ.X k) _ ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫ Functor.mapDerivedCategoryNatIso q

/-- Native normalization of the actual `PointData`, including the change of scalar
coordinates. The ordinary identification is evaluation at 1, and the restriction cup
is fixed on pure tensors and by every chain/localization square. In particular the
native comparison is not a second, unrelated family of point tensor isomorphisms.
Source: geometric-point evaluation and the native section cup, proof Step 1
(blueprint: lem-sf-point-fibre-qbar-scalar-coherence). -/
structure QbarPointNativeData (Λ : ScalarSixRing.{u}) (k : Type u) [Field k] [IsAlgClosed k]
    (point : PointData Λ k) where
  sectionsIso : condensedRingCoefficientSections Λ.X (Spec (.of k)) ⋙
    qbarNativeRestriction Λ ≅ CohomologyTransport.sections Λ.X (Spec (.of k))
  sections_apply (M : ModuleRingedComparison.internalModules Λ.X (Spec (.of k)))
      (f : (condensedRingCoefficientSections Λ.X (Spec (.of k))).obj M) :
    (sectionsIso.hom.app M) f =
      (((constantSheafAdj (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1}
        (MorphismProperty.Over.mkIdTerminal @WeaklyEtale (Spec (.of k)))).homEquiv
          (𝟙_ Ab.{u + 1}) M.X) (η[condensedRingObj Λ.X (Spec (.of k))] ≫ f.hom)).hom
            (ULift.up 1)
  restrictionCup : ExactSectionsDerivedCup (qbarNativeRestriction Λ)
  restriction_tensor (M N : ModuleCat.{u + 1} (MonObj.Γ Λ.X)) (x : M) (y : N) :
    (restrictionCup.ordinary.μ M N).hom (x ⊗ₜ[condensedScalarRing Λ.X] y) =
      x ⊗ₜ[MonObj.Γ Λ.X] y
  restriction_unit (r : condensedScalarRing Λ.X) :
    restrictionCup.ordinary.ε.hom r =
      (InternalAbelianSheafModule.sectionGlobalEquiv
        (coherentTopology Profinite.{u}) Λ.X (⊤_ Profinite.{u}) terminalIsTerminal).symm r
  tensor_exact (M N : CohomologyTransport.D Λ.X (Spec (.of k)))
      (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M)
      (hN : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N) :
    (point.tensorIso M N hM hN).inv = (pairingExactScalarPointCup Λ.X k).derived.μ M N
  unit_exact : point.unitIso.inv = (pairingExactScalarPointCup Λ.X k).derived.ε
  tensor_native (M N : CohomologyTransport.D Λ.X (Spec (.of k)))
      (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M)
      (hN : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N) :
    (point.tensorIso M N hM hN).inv =
      ((qbarNativeFiberIso Λ k sectionsIso).inv.app M ⊗ₘ
        (qbarNativeFiberIso Λ k sectionsIso).inv.app N) ≫
      restrictionCup.derived.μ ((TraceCupPoint.fiber Λ.X k).obj M)
        ((TraceCupPoint.fiber Λ.X k).obj N) ≫
      (qbarNativeRestriction Λ).mapDerivedCategory.map (TraceCupPoint.tensor Λ.X k M N) ≫
      (qbarNativeFiberIso Λ k sectionsIso).hom.app (M ⊗ N)
  unit_native : point.unitIso.inv = restrictionCup.derived.ε ≫
    (qbarNativeRestriction Λ).mapDerivedCategory.map (pointCoefficientUnit Λ.X k) ≫
      (qbarNativeFiberIso Λ k sectionsIso).hom.app (𝟙_ _)

end AlgebraicGeometry.ProEtale.CondensedRing
