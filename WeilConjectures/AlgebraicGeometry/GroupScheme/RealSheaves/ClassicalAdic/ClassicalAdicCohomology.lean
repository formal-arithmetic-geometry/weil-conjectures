/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.AlgebraicGeometry.CoefficientHomComparison.ConstructibleCoefficientHomComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
import WeilConjectures.Compactification.BoundaryRefinement
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.AlgebraicGeometry.AffineFreeEtaleModuleFamilyModels
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldFiniteTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.AlgebraicGeometry.Affine.AffineEtaleFreeDetection
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.CategoryTheory.Skeletal
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageBoundedBelow
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalBounds
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedPoint.NativeCondensedPointSections
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralPositiveReductionConstructible
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralTensorConstructibility
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleObjectProductsExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedLowerStarDerivedLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.SixFunctors.Supporting.DerivedLimitTriangleTransport

/-! # Classical adic cohomology of a constructible Weil complex

Source: latest blueprint, part-weights-riemann-hypothesis/sec-rank-one-curves/
sec-the-jacobian-and-frobenius-invariants/sk-prop-wrp-h1-no-fixed/d-real-cohom.md,
Comparison with the classical description (blueprint: prop-wf-classical-adic-cohomology).

The helpers expose existing coefficient transports and bundle the displayed comparisons.
All finite levels are positive: the sequence index n denotes the quotient by pi^(n+1).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace RealSheaves

/-- The existing finite-field datum underlying the chapter setup.
Source: d-real-setup and the comparison paragraph
(blueprint: prop-wf-classical-adic-cohomology). -/
def Setup.adicFieldDatum (D : Setup.{u, v}) : WeilConjectures.FiniteFieldDatum.{u} where
  p := D.p
  a := D.a
  q := D.q
  prime := D.p_prime
  exponent_pos := D.a_pos
  cardinality_eq := rfl
  k₀ := D.k₀
  card_base := Nat.card_eq_fintype_card.trans D.card_eq
  k := D.k

/-- Geometric Frobenius g_C = id × Spec(φ_q⁻¹) on the chapter's chosen fibre product:
exactly the recorded `FiniteFieldDatum.geometricFrobenius` of def-weil-frobenius-detailed,
which def-weil-weil-sheaf-complex uses for Weil structures; no second definition.
Source: d-real-setup, geometric Frobenius convention; def-weil-frobenius-detailed
(blueprint: prop-wf-classical-adic-cohomology). -/
abbrev Setup.adicFrobenius (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) : Aut (D.geometricCurve C₀) :=
  @WeilConjectures.FiniteFieldDatum.geometricFrobenius D.adicFieldDatum
    (Over.mk (C₀ ↘ Spec (.of D.k₀))) hC.2.2.2.1 hC.2.2.2.2.1

private theorem bounded_comap_iso {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (f : S ⟶ R) [IsMonHom f] [IsIso f]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R))
    (hK : boundedConstructible R K) :
    boundedConstructible S ((Mod.comap f).mapDerivedCategory.obj K) := by
  refine ⟨(Mod.comap f).bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
  exact constructible_of_iso
    ((Mod.comap f).mapDerivedCategoryHomologyFunctorIso n |>.app K)
    (constructible_comap f (hK.2 n))

namespace ClassicalAdic

/-- The canonical spectral integral-to-field map is the existing coefficient comparison.
Source: comparison paragraph (blueprint: prop-wf-classical-adic-cohomology). -/
abbrev integralToField := AlgebraicGeometry.ProEtale.CoefficientHomComparison.integralToField

/-- Derived coefficient change on the actual pulled-back coefficient sheaves.
Source: comparison paragraph, scalar extension
(blueprint: prop-wf-classical-adic-cohomology). -/
abbrev extend {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (φ : Λ ⟶ Λ') [IsMonHom φ] (X : Scheme.{u}) :=
  (Mod.extendScalars (coefficientMap φ X)).leftDerivedFunctor

/-- Derived scalar extension on coefficient complexes, using the induced global ring map.
Source: comparison paragraph, the coefficient-valued displayed formulas
(blueprint: prop-wf-classical-adic-cohomology). -/
abbrev extendSections {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (φ : Λ ⟶ Λ') [IsMonHom φ] :=
  letI := ModuleCat.extendScalars_preservesKFlatQuasiIso (CategoryTheory.MonObj.Γ.map φ)
  (ModuleCat.extendScalars (CategoryTheory.MonObj.Γ.map φ)).leftDerivedFunctor

private theorem models (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ell : ℕ) [Fact ell.Prime]
    (K : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X)) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField ell)
      (K_E : BoundedConstructible (condensedRingObj
        (Profinite.continuousMapRingObj E.val) X))
      (K₀ : BoundedConstructible (AdicCompletion.ring ell (ULift.{u} E.val) X)),
      Nonempty ((derivedExtendScalarsToPadicAlgCl X ell E).obj K_E.obj ≅ K.obj) ∧
      Nonempty ((extend (CoefficientHomComparison.integralToField ell E) X).obj
        K₀.obj ≅ K_E.obj) := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  obtain ⟨E, K_E, ⟨eE⟩⟩ := constructibleCocone_essSurjObj X ell K
  obtain ⟨M, ⟨eM⟩⟩ := exists_boundedConstructibleExtendScalars_obj_iso X ell E K_E
  let e := CoefficientHomComparison.integralIso.{u} ell E
  let : IsGrothendieckAbelian.{u + 1}
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) := inferInstance
  let F := Mod.comap.{u + 1, u + 1, u + 2, u + 2} (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap.{u} e.inv X)
  let M₀ := F.mapDerivedCategory.{u + 1, u + 1}.obj M.obj
  have hM₀ : boundedConstructible (AdicCompletion.ring ell (ULift.{u} E.val) X) M₀ :=
    bounded_comap_iso _ _ M.property
  let f := coefficientMap.{u} e.hom X
  let g := coefficientMap.{u} (CoefficientHomComparison.integralToField ell E) X
  let h := padicIntegersToPadicSubfield X ell E
  have hcomp : f ≫ g = h := by
    dsimp [f, g, h, CoefficientHomComparison.integralToField]
    rw [← coefficientMap_comp]
    simp [e]
  have : PreservesFiniteLimits (Mod.extendScalars f) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv f).symm
  have hinv : (asIso f).inv = coefficientMap e.inv X := by
    apply IsIso.inv_eq_of_hom_inv_id
    change coefficientMap e.hom X ≫ coefficientMap e.inv X = 𝟙 _
    rw [← coefficientMap_comp]
    simp
  let ef : Mod.extendScalars f ≅ F := by
    dsimp only [F]
    exact Mod.extendScalarsIsoComapInv f ≪≫ Mod.comapCongr hinv
  let eF : (Mod.extendScalars.{u + 1, u + 2} f).leftDerivedFunctor ≅
      F.mapDerivedCategory.{u + 1, u + 1} :=
    (Mod.extendScalars.{u + 1, u + 2} f).leftDerivedFunctorIsoMapDerivedCategory.{u + 1, u + 1} ≪≫
      Functor.mapDerivedCategoryNatIso ef
  refine ⟨E, K_E, ⟨M₀, hM₀⟩, ?_, ?_⟩
  · exact ⟨(boundedConstructible _).ι.mapIso eE⟩
  · exact ⟨(Mod.extendScalars.{u + 1, u + 2} g).leftDerivedFunctor.mapIso (eF.symm.app M.obj) ≪≫
      (Mod.derivedExtendScalarsCompIso.{u + 1, u + 2} f g h hcomp).symm.app M.obj ≪≫
      (boundedConstructible _).ι.mapIso eM⟩

/-- The two coefficient-complex scalar comparisons, for one specified coefficient change.
Source: comparison paragraph, the rational and finite formulas and their compact analogues
(blueprint: prop-wf-classical-adic-cohomology). -/
def ScalarComparisons {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (φ : Λ ⟶ Λ') [IsMonHom φ] {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X))) : Prop :=
  Nonempty ((extendSections φ).obj
      ((CondensedRing.condensedRingOrdinaryCoefficientComplex Λ a).obj K) ≅
    (CondensedRing.condensedRingOrdinaryCoefficientComplex Λ' a).obj L) ∧
  Nonempty ((extendSections φ).obj
      ((CondensedRing.condensedRingCompactCoefficientComplex Λ c).obj K) ≅
    (CondensedRing.condensedRingCompactCoefficientComplex Λ' c).obj L)

/-- The finite-level comparison retains the quotient-ring action in every calculation.
The normalized encoding is the existing section-action equivalence; quantification over
its witnesses avoids choosing an arbitrary presentation. Both compact calculations use
exactly the supplied compactification.
Source: comparison paragraph, finite torsion levels
(blueprint: prop-wf-classical-adic-cohomology). -/
def EtaleComparisons (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A X)) : Prop :=
  ∀ (eX : FiniteDiscreteOrdinary.Encoding A X)
    (eY : FiniteDiscreteOrdinary.Encoding A Y),
    let M := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let L := eX.fixedDerived.functor.obj K
    IsIso ((derivedComparisonAdjunction M X).counit.app L) ∧
    Nonempty ((comparisonUpperStar M Y).mapDerivedCategory.obj
      ((Etale.lowerStar M a).rightDerivedFunctor.obj
        ((comparisonLowerStar M X).rightDerivedFunctor.obj L)) ≅
      eY.fixedDerived.functor.obj
        (((CondensedRing.lowerStar
          (FiniteDiscreteOrdinary.coefficient A) a).rightDerivedFunctor).obj K)) ∧
    Nonempty ((comparisonUpperStar M Y).mapDerivedCategory.obj
      ((Etale.rightDerivedLowerShriekOfCompactification M c).obj
        ((comparisonLowerStar M X).rightDerivedFunctor.obj L)) ≅
      eY.fixedDerived.functor.obj
        ((CondensedRing.rightDerivedLowerShriekOfCompactification
          (FiniteDiscreteOrdinary.coefficient A) c).obj K))

private theorem etale_comparisons
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A] {X Y : Scheme.{u}} [IsNoetherian X]
    {a : X ⟶ Y} [QuasiCompact a] [QuasiSeparated a] (c : Compactification a)
    (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A X))
    (hK : constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X K) :
    EtaleComparisons A c K := by
  intro eX eY
  let M := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let U := (comparisonUpperStar M X).mapDerivedCategory
  let R := (comparisonLowerStar M X).rightDerivedFunctor
  let L := eX.fixedDerived.functor.obj K
  let adj := derivedComparisonAdjunction M X
  obtain ⟨J, hJ, ⟨z⟩⟩ := (fixedCriterion A X eX K).mp hK
  have hu : IsIso (adj.unit.app J) :=
    isIso_derivedComparisonAdjunction_unit_app M X J hJ.1.1
  have hc : IsIso (adj.counit.app (U.obj J)) :=
    isIso_of_hom_comp_eq_id _ (adj.left_triangle_components J)
  have hcL : IsIso (adj.counit.app L) := by
    rw [← NatTrans.isIso_app_iff_of_iso adj.counit z]
    exact hc
  let r : R.obj L ≅ J := R.mapIso z.symm ≪≫ (asIso (adj.unit.app J)).symm
  let jp : DerivedCategory.Plus (Sheaf X.smallEtaleTopology M) := ⟨J, hJ.1.1⟩
  let push := FiniteDiscreteOrdinary.encodingDerivedPushforwardIso A a eY eX
  let eZ := (FiniteDiscreteOrdinary.encoding_exists A c.Z).some
  let comp : CondensedRing.rightDerivedLowerShriekOfCompactification
      (FiniteDiscreteOrdinary.coefficient A) c ⋙ eY.fixedDerived.functor ≅
      eX.fixedDerived.functor ⋙ rightDerivedLowerShriekOfCompactification M c :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (FiniteDiscreteOrdinary.encodingDerivedPushforwardIso A c.g eY eZ) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (FiniteDiscreteOrdinary.encodingDerivedOpenShriekIso A c.i eZ eX) _ ≪≫
      Functor.associator _ _ _
  refine ⟨hcL, ⟨?_⟩, ⟨?_⟩⟩
  · exact ((Etale.lowerStar M a).rightDerivedFunctor ⋙
      (comparisonUpperStar M Y).mapDerivedCategory).mapIso r ≪≫
      ((rightDerivedLowerStarComparisonIso M a).app jp).symm ≪≫
      (lowerStar M a).rightDerivedFunctor.mapIso z ≪≫ (push.app K).symm
  · exact (Etale.rightDerivedLowerShriekOfCompactification M c ⋙
      (comparisonUpperStar M Y).mapDerivedCategory).mapIso r ≪≫
      ((rightDerivedLowerShriekOfCompactificationComparisonIso M c).app jp).symm ≪≫
      (rightDerivedLowerShriekOfCompactification M c).mapIso z ≪≫ (comp.app K).symm

/-- Reconstruction with the canonical derived quotient projections, not an unspecified cone.
Source: comparison paragraph, RΓ commuting with derived limits and the compact analogue
(blueprint: prop-wf-classical-adic-cohomology). -/
def TowerReconstruction (D : Setup.{u, v})
    (E : PadicAlgCl.FiniteIntermediateField D.l) (X : Scheme.{u})
    (F : DerivedCategory (AdicCompletion.Modules D.l (ULift.{u} E.val) X) ⥤
      DerivedCategory (ModuleCat.{u + 1}
        (CategoryTheory.MonObj.Γ (DerivedNakayama.integerRing D.l (ULift.{u} E.val)))))
    (K : DerivedCategory (AdicCompletion.Modules D.l (ULift.{u} E.val) X)) : Prop :=
  ∃ δ : (∏ᶜ fun n ↦ F.obj
      (AdicCompletion.integralLevel D.l (ULift.{u} E.val) X K n)) ⟶ (F.obj K)⟦(1 : ℤ)⟧,
    IsDerivedLimitTriangle
      (K := fun n ↦ F.obj (AdicCompletion.integralLevel D.l (ULift.{u} E.val) X K n))
      (fun n ↦ F.map (AdicCompletion.integralStep D.l (ULift.{u} E.val) X K n))
      (F.obj K)
      (Pi.lift (fun n ↦ F.map
        ((Mod.derivedExtendMapDerivedCategoryAdjunction
          (AdicCompletion.quotient D.l (ULift.{u} E.val) X n)).unit.app K))) δ

private theorem tower_transport
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasProductsOfShape ℕ C] {A B : ℕ → C}
    (f : ∀ n, A (n + 1) ⟶ A n) (g : ∀ n, B (n + 1) ⟶ B n)
    (e : ∀ n, A n ≅ B n)
    (he : ∀ n, (e (n + 1)).hom ≫ g n = f n ≫ (e n).hom)
    (L : C) (p : ∀ n, L ⟶ A n) (q : ∀ n, L ⟶ B n)
    (hq : ∀ n, p n ≫ (e n).hom = q n)
    (δ : ∏ᶜ A ⟶ L⟦(1 : ℤ)⟧)
    (hδ : IsDerivedLimitTriangle f L (Pi.lift p) δ) :
    ∃ ε, IsDerivedLimitTriangle g L (Pi.lift q) ε := by
  let b : ∏ᶜ A ≅ ∏ᶜ B := Pi.mapIso e
  have hp : Pi.lift p ≫ b.hom = Pi.lift q := by
    apply Pi.hom_ext
    intro n
    simp [b, Category.assoc, hq]
  have hb : b.hom ≫ towerTransitionEndomorphism g =
      towerTransitionEndomorphism f ≫ b.hom :=
    towerTransitionEndomorphism_natural_backward f g (fun n ↦ (e n).hom) he
  refine ⟨b.inv ≫ δ, ?_⟩
  let T₁ := Pretriangulated.Triangle.mk (Pi.lift p)
    (towerTransitionEndomorphism f) δ
  let T₂ := Pretriangulated.Triangle.mk (Pi.lift q)
    (towerTransitionEndomorphism g) (b.inv ≫ δ)
  apply Pretriangulated.isomorphic_distinguished T₁ hδ T₂
  refine Pretriangulated.Triangle.isoMk T₂ T₁ (Iso.refl _) b.symm b.symm ?_ ?_ ?_
  · change Pi.lift q ≫ b.inv = 𝟙 _ ≫ Pi.lift p
    rw [← hp]
    simp
  · change towerTransitionEndomorphism g ≫ b.inv =
      b.inv ≫ towerTransitionEndomorphism f
    apply (cancel_mono b.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using (congrArg (fun t ↦ b.inv ≫ t) hb.symm).symm
  · change (b.inv ≫ δ) ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 L) = b.inv ≫ δ
    simp

private theorem sections_products
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    PreservesLimitsOfShape (Discrete ℕ)
      (CondensedRing.condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctor := by
  let S := CondensedRing.condensedRingCoefficientSections Λ (Spec (.of k))
  have := (CondensedRing.finite_point_sections_exact Λ k).1
  have := (CondensedRing.finite_point_sections_exact Λ k).2
  have : PreservesLimitsOfShape (Discrete ℕ) S := by
    have : PreservesLimitsOfShape (Discrete ℕ)
        (S ⋙ forget₂ (ModuleCat.{u + 1} (MonObj.Γ Λ)) Ab.{u + 1}) :=
      inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
        (preadditiveCoyonedaObj (Mod.regular (condensedRingObj Λ (Spec (.of k)))) ⋙
          forget₂ _ Ab.{u + 1}))
    exact preservesLimitsOfShape_of_reflects_of_preserves S
      (forget₂ (ModuleCat.{u + 1} (MonObj.Γ Λ)) Ab.{u + 1})
  have := proEtale_moduleObject_products_exact (Spec (.of k))
    (condensedRingObj Λ (Spec (.of k))) (ULift.{u + 1} ℕ)
  have := HasExactLimitsOfShape.of_domain_equivalence
    (Discrete.equivalence (Equiv.ulift.{u + 1, 0} (α := ℕ)))
    (C := Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))
  have : PreservesLimitsOfShape (Discrete ℕ) S.mapDerivedCategory :=
    derived_products_of_Q ℕ S
  exact preservesLimitsOfShape_of_natIso S.rightDerivedFunctorIsoMapDerivedCategory.symm

private theorem ordinary_products
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) :
    PreservesLimitsOfShape (Discrete ℕ)
      (CondensedRing.condensedRingOrdinaryCoefficientComplex Λ a) := by
  have := sections_products Λ k
  change PreservesLimitsOfShape (Discrete ℕ) (_ ⋙ _)
  infer_instance

private theorem mapped_product_lift
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    (T : ℕ → A) [HasProduct T] [HasProduct (fun n ↦ F.obj (T n))]
    (e : F.obj (∏ᶜ T) ≅ ∏ᶜ fun n ↦ F.obj (T n))
    (he : ∀ n, e.hom ≫ Pi.π _ n = F.map (Pi.π T n))
    {L : A} (p : L ⟶ ∏ᶜ T) (a : ∀ n, L ⟶ T n) (hp : p = Pi.lift a) :
    F.map p ≫ e.hom = Pi.lift (fun n ↦ F.map (a n)) := by
  subst p
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, he, ← F.map_comp, Pi.lift_π]

private theorem tower_of_preserves_products (D : Setup.{u, v})
    (E : PadicAlgCl.FiniteIntermediateField D.l) (X : Scheme.{u})
    (F : DerivedCategory (AdicCompletion.Modules D.l (ULift.{u} E.val) X) ⥤
      DerivedCategory (ModuleCat.{u + 1}
        (CategoryTheory.MonObj.Γ (DerivedNakayama.integerRing D.l (ULift.{u} E.val)))))
    [F.CommShift ℤ] [F.IsTriangulated] [PreservesLimitsOfShape (Discrete ℕ) F]
    (K : DerivedCategory (AdicCompletion.Modules D.l (ULift.{u} E.val) X))
    (hK : IsDerivedComplete D.l (ULift.{u} E.val) X K) :
    TowerReconstruction D E X F K := by
  have hcomplete := hK
  obtain ⟨P, hP, ⟨e⟩, _⟩ := hK
  have hc := (AdicCompletion.isDerivedComplete_iff D.l (ULift.{u} E.val) X K P hP e).mp hcomplete
  let c := asIso (AdicCompletion.completionMap D.l (ULift.{u} E.val) X K P e)
  obtain ⟨p, δ, hδ, hp⟩ :=
    AdicCompletion.roos_isDerivedLimit D.l (ULift.{u} E.val) X K P hP e
  let q := c.hom ≫ p
  let ε := δ ≫ (shiftFunctor _ (1 : ℤ)).map c.inv
  have hε := derivedLimitTriangleTransport
    (AdicCompletion.integralStep D.l (ULift.{u} E.val) X K) c p δ hδ
  obtain ⟨b, hb, ht⟩ := F.isDerivedLimitTriangle_map
    (AdicCompletion.integralStep D.l (ULift.{u} E.val) X K) K q ε hε
  have hq := mapped_product_lift F _ b hb q
    (fun n ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction
      (AdicCompletion.quotient D.l (ULift.{u} E.val) X n)).unit.app K) hp
  exact ⟨_, hq ▸ ht⟩

end ClassicalAdic

/-- Classical adic reconstruction for ordinary and compact cohomology of a Weil complex.

Source: latest blueprint, part-weights-riemann-hypothesis/sec-rank-one-curves/
sec-the-jacobian-and-frobenius-invariants/sk-prop-wrp-h1-no-fixed/d-real-cohom.md,
Comparison with the classical description
(blueprint: prop-wf-classical-adic-cohomology).

Proof: (1) Forget the Weil structure. The finite-extension two-colimit gives E and K_E;
the integral-model generators and rationalization comparison give an integral K_0.
(2) The integral criterion gives completeness and finite Tor amplitude. Apply scalar-six
to O_E -> E -> Qbar and to the positive uniformizer quotients. Exact terminal sections
over the algebraically closed point, and ringed evaluation on flat/Koszul models, give
the coefficient-complex comparisons, compatibly with the quotient maps.
(3) Completeness identifies K_0 with its derived reduction tower. Global derived Hom
from the regular unit preserves derived limits, yielding ordinary reconstruction.
(4) For compact support, constructibility stability makes Ra_! K_0 complete on the point.
Apply the same limit argument there and identify its reductions by scalar-six; this
does not assert that Ra_! preserves arbitrary inverse limits.
(5) Finite admissible comparison identifies each positive level and both operations
with the etale calculations using the same compactification.
(6) Substitute the limit descriptions in the rational scalar comparisons and take H^i.
This is the classical adic construction in every degree, without interchanging H^i
and an underived inverse limit. Qbar is represented by the existing PadicAlgCl model;
the chapter's chosen algebraic closure is identified with it over Q_l.
-/
theorem classicalAdicCohomology (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀)
    (c : Compactification
      (pullback.snd (C₀ ↘ Spec (.of D.k₀))
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    (K : WeilConjectures.condensedWeilComplex (Profinite.padicAlgClRingObj D.l)
      (D.adicFrobenius C₀ hC).hom) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField D.l)
      (K_E : BoundedConstructible (condensedRingObj
        (Profinite.continuousMapRingObj E.val) (D.geometricCurve C₀)))
      (K₀ : BoundedConstructible (AdicCompletion.ring D.l (ULift.{u} E.val)
        (D.geometricCurve C₀))),
      Nonempty ((ClassicalAdic.extend (Profinite.padicSubfieldRingObjToPadicAlgCl D.l E)
          (D.geometricCurve C₀)).obj K_E.obj ≅
        ((WeilConjectures.condensedWeilForget (Profinite.padicAlgClRingObj D.l)
          (D.adicFrobenius C₀ hC).hom).obj K).obj) ∧
      Nonempty ((ClassicalAdic.extend
          (AlgebraicGeometry.ProEtale.CoefficientHomComparison.integralToField D.l E)
          (D.geometricCurve C₀)).obj K₀.obj ≅ K_E.obj) ∧
      IsDerivedComplete D.l (ULift.{u} E.val) (D.geometricCurve C₀) K₀.obj ∧
      ClassicalAdic.ScalarComparisons
        (ClassicalAdic.integralToField D.l E ≫
          Profinite.padicSubfieldRingObjToPadicAlgCl D.l E) c K₀.obj
        (((WeilConjectures.condensedWeilForget (Profinite.padicAlgClRingObj D.l)
          (D.adicFrobenius C₀ hC).hom).obj K).obj) ∧
      (∀ n : ℕ, ClassicalAdic.ScalarComparisons
        (DerivedNakayama.reductionRing D.l (ULift.{u} E.val) (n + 1)) c K₀.obj
        ((AdicCompletion.derivedReduction D.l (ULift.{u} E.val)
          (D.geometricCurve C₀) n).obj K₀.obj)) ∧
      ClassicalAdic.TowerReconstruction D E (D.geometricCurve C₀)
        (CondensedRing.condensedRingOrdinaryCoefficientComplex
          (DerivedNakayama.integerRing D.l (ULift.{u} E.val))
          (pullback.snd (C₀ ↘ Spec (.of D.k₀))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))) K₀.obj ∧
      ClassicalAdic.TowerReconstruction D E (D.geometricCurve C₀)
        (CondensedRing.condensedRingCompactCoefficientComplex
          (DerivedNakayama.integerRing D.l (ULift.{u} E.val)) c) K₀.obj ∧
      ∀ n : ℕ,
        letI nf := (Padic.coefficientExtensionAbsoluteValue D.l (ULift.{u} E.val)).toNormedField
        letI : TopologicalSpace (ULift.{u} E.val) :=
          nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        ClassicalAdic.EtaleComparisons
        (Padic.coefficientExtensionRing D.l (ULift.{u} E.val) (n + 1)) c
        ((AdicCompletion.derivedReduction D.l (ULift.{u} E.val)
          (D.geometricCurve C₀) n).obj K₀.obj) := by
  have : IsSeparated (C₀ ↘ Spec (.of D.k₀)) := hC.2.1
  have : LocallyOfFiniteType (C₀ ↘ Spec (.of D.k₀)) := hC.2.2.2.1
  have : QuasiCompact (C₀ ↘ Spec (.of D.k₀)) := hC.2.2.2.2.1
  let a := pullback.snd (C₀ ↘ Spec (.of D.k₀))
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  have : LocallyOfFiniteType a := inferInstance
  have : QuasiCompact a := inferInstance
  have : IsLocallyNoetherian (D.geometricCurve C₀) :=
    LocallyOfFiniteType.isLocallyNoetherian a
  have : CompactSpace (D.geometricCurve C₀) :=
    QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian (D.geometricCurve C₀) := ⟨⟩
  let L := (WeilConjectures.condensedWeilForget (Profinite.padicAlgClRingObj D.l)
    (D.adicFrobenius C₀ hC).hom).obj K
  obtain ⟨E, K_E, K₀, hE, h₀⟩ := ClassicalAdic.models (D.geometricCurve C₀) D.l L
  have hconst : constantModelBoundedConstructible
      (DerivedNakayama.integerRing D.l (ULift.{u} E.val)) (D.geometricCurve C₀) K₀.obj :=
    ⟨K₀.property.1, fun q ↦
      (integerConstructibleComparison D.l (ULift.{u} E.val) (D.geometricCurve C₀) _).mp
        (K₀.property.2 q)⟩
  have hcomplete := ((condensed_integral_criterion D.l (ULift.{u} E.val)
    (D.geometricCurve C₀) K₀.obj).out 0 1).mp hconst
  have hsc := classicalAdicScalarComparisons D E a c K₀.obj hconst
  let i := ClassicalAdic.integralToField D.l E
  let j := Profinite.padicSubfieldRingObjToPadicAlgCl D.l E
  obtain ⟨eE⟩ := hE
  obtain ⟨e₀⟩ := h₀
  let e : (ClassicalAdic.extend (i ≫ j) (D.geometricCurve C₀)).obj K₀.obj ≅ L.obj :=
    (Mod.derivedExtendScalarsCompIso (coefficientMap i (D.geometricCurve C₀))
      (coefficientMap j (D.geometricCurve C₀))
      (coefficientMap (i ≫ j) (D.geometricCurve C₀))
      (coefficientMap_comp i j (D.geometricCurve C₀)).symm).app K₀.obj ≪≫
    (ClassicalAdic.extend j (D.geometricCurve C₀)).mapIso e₀ ≪≫ eE
  refine ⟨E, K_E, K₀, ⟨eE⟩, ⟨e₀⟩, hcomplete.1, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨hsc.1.1.some ≪≫
      (CondensedRing.condensedRingOrdinaryCoefficientComplex
        (Profinite.padicAlgClRingObj D.l) a).mapIso e⟩,
      ⟨hsc.1.2.some ≪≫ (CondensedRing.condensedRingCompactCoefficientComplex
        (Profinite.padicAlgClRingObj D.l) c).mapIso e⟩⟩
  · exact hsc.2
  · have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    have := ClassicalAdic.ordinary_products
      (DerivedNakayama.integerRing D.l (ULift.{u} E.val)) D.k a
    let F := CondensedRing.condensedRingOrdinaryCoefficientComplex
      (DerivedNakayama.integerRing D.l (ULift.{u} E.val)) a
    letI : F.CommShift ℤ := by
      dsimp [F, CondensedRing.condensedRingOrdinaryCoefficientComplex]
      infer_instance
    letI : F.IsTriangulated := by
      dsimp [F, CondensedRing.condensedRingOrdinaryCoefficientComplex]
      infer_instance
    exact ClassicalAdic.tower_of_preserves_products D E (D.geometricCurve C₀)
      F K₀.obj hcomplete.1
  · have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    let Y := Spec (.of D.k)
    let O := DerivedNakayama.integerRing D.l (ULift.{u} E.val)
    let G := CondensedRing.rightDerivedLowerShriekOfCompactification O c
    let S := (CondensedRing.condensedRingCoefficientSections O Y).rightDerivedFunctor
    let M := G.obj K₀.obj
    have := ClassicalAdic.sections_products O D.k
    have hM := classicalAdicCompactOutputComplete D E a c K₀.obj hconst
    obtain ⟨δ, hδ⟩ := ClassicalAdic.tower_of_preserves_products D E Y S M hM
    obtain ⟨e, he, hp⟩ := classicalAdicCompactTowerComparison D E a c K₀.obj hconst
    have heS (n : ℕ) :
        (S.mapIso (e (n + 1))).hom ≫
            S.map (G.map (AdicCompletion.integralStep D.l (ULift.{u} E.val)
              (D.geometricCurve C₀) K₀.obj n)) =
          S.map (AdicCompletion.integralStep D.l (ULift.{u} E.val) Y M n) ≫
            (S.mapIso (e n)).hom := by
      simpa only [Functor.mapIso_hom, ← S.map_comp] using congrArg S.map (he n)
    have hpS (n : ℕ) :
        S.map ((Mod.derivedExtendMapDerivedCategoryAdjunction
          (AdicCompletion.quotient D.l (ULift.{u} E.val) Y n)).unit.app M) ≫
          (S.mapIso (e n)).hom =
        S.map (G.map ((Mod.derivedExtendMapDerivedCategoryAdjunction
          (AdicCompletion.quotient D.l (ULift.{u} E.val) (D.geometricCurve C₀) n)).unit.app
            K₀.obj)) := by
      simpa only [Functor.mapIso_hom, ← S.map_comp] using congrArg S.map (hp n)
    exact ClassicalAdic.tower_transport _ _ (fun n ↦ S.mapIso (e n)) heS (S.obj M)
      _ _ hpS δ hδ
  · intro n
    let nf := (Padic.coefficientExtensionAbsoluteValue D.l (ULift.{u} E.val)).toNormedField
    let : TopologicalSpace (ULift.{u} E.val) :=
      nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    let A := Padic.coefficientExtensionRing D.l (ULift.{u} E.val) (n + 1)
    let : Finite A := Padic.finite_coefficientExtensionRing D.l (ULift.{u} E.val)
      (n + 1) (by omega)
    let : DiscreteTopology A := finiteTopology_discrete D.l (ULift.{u} E.val) n
    exact ClassicalAdic.etale_comparisons A c _
      (integralReduction_constantModelBoundedConstructible D.l (ULift.{u} E.val)
        (D.geometricCurve C₀) K₀.obj hconst n)

end RealSheaves
