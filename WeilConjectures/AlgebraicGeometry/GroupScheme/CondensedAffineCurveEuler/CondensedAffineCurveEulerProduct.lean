/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedDerived.CondensedScalarDerivedLocalFrobenius
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Complex.Basic
public import Mathlib.Order.KrullDimension
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import WeilConjectures.SmoothPurity.WeilSheafComplex
import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedDerived.CondensedScalarDerivedLocalFrobenius
import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Complex.Basic
import Mathlib.Order.KrullDimension
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.PowerSeries.Trunc
import WeilConjectures.PointCount
import WeilConjectures.ZetaLinearAlgebra.AlternatingEulerProduct
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.PoincareDuality.Abstract
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import Mathlib.Topology.KrullDimension
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension
import Mathlib.Algebra.Field.ULift
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import Mathlib.Algebra.Ring.Shrink
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointScalarRealization
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Conv
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
import WeilConjectures.PoincareDuality.VerdierBiduality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteConstructibleEncoding
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageBoundedBelow
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Field.Equiv
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.PathCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.Sections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointTrivializationComposition
import WeilConjectures.CategoryTheory.PullbackFamily
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import WeilConjectures.SmoothPurity.CondensedWeilModules
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeTerminalSectionsComparison
import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Euler product on a smooth geometrically connected affine curve

Source: literature/blueprint/latest/blueprint/sec-purity-real-sheaves/
sk-p-real-rankin/cor-rp-euler-product.md and its two-paragraph proof
(blueprint: cor-rp-euler-product).

The Euler product, determinant and global operator are the recorded condensed constructions.
The helper only places the given constructible Weil sheaf in degree zero.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedAffineCurveEuler

attribute [local instance] IsAlgClosure.isAlgClosed

/-- A constructible Weil sheaf in degree zero, with its actual Weil structure.
Source: cor-rp-euler-product, first proof paragraph, K = G in degree zero
(blueprint: cor-rp-euler-product). -/
def sheafComplex (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (U₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    (G : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius U₀).hom) :
    strictWeilComplexCategory D ell hEll U₀ .qbar :=
  ⟨CategoryTheory.Endofunctor.IsoAlgebra.mk
    ((DerivedCategory.singleFunctor _ 0).obj G.obj.carrier)
    (((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius U₀).hom).mapDerivedCategorySingleFunctor 0).app G.obj.carrier ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso G.obj.str),
    (condensedWeilSingle ell (D.geometricFrobenius U₀).hom G).property⟩

private theorem dimension_le_one (X : Scheme.{u}) (h : X.IsPureDimension 1) :
    topologicalKrullDim X ≤ 1 := by
  let := specializationOrder X
  rw [topologicalKrullDim_eq_krullDim_specializationOrder, Order.krullDim_eq_iSup_height]
  refine iSup_le fun x ↦ ?_
  let C := irreducibleComponent x
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have hsub : closure ({x} : Set X) ⊆ C :=
    closure_minimal (Set.singleton_subset_iff.mpr mem_irreducibleComponent)
      (isClosed_of_mem_irreducibleComponents C hC)
  rw [← topologicalKrullDim_closure_singleton]
  exact ((Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le).trans
    (h C hC).le

attribute [-instance] WeilConjectures.integralOperationsSiteSmall in
private theorem sections_zero_of_fieldFiber
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [IsAlgClosed k]
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (Spec (.of k))))
    (h : IsZero ((CondensedQbarGeometricEvaluation.fieldFiber k ell).obj M)) :
    IsZero ((CondensedRing.condensedRingCoefficientSections
      (Profinite.padicAlgClRingObj ell) (Spec (.of k))).obj M) := by
  let Λ := Profinite.padicAlgClRingObj ell
  let Y := Spec (.of k)
  obtain ⟨e⟩ := CondensedRing.native_terminalSectionsIso.{u}
    (A := CategoryTheory.MonObj.Γ Λ) (Scheme.ProEt.topology Y)
    (condensedRingObj Λ Y) (CondensedRing.condensedRingScalarSections Λ Y)
    (Scheme.ProEt.mk (𝟙 Y))
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale Y)
  let T := CondensedRing.Evaluation.sections (Scheme.ProEt.topology Y)
    (condensedRingObj Λ Y) (Scheme.ProEt.mk (𝟙 Y))
  have hs := ModuleCat.subsingleton_of_isZero h
  have : Subsingleton (T.obj M) := hs
  have hz : IsZero (T.obj M) := ModuleCat.isZero_of_subsingleton _
  exact ((ModuleCat.restrictScalars _).map_isZero hz).of_iso (e.app M)

end WeilConjectures.CondensedAffineCurveEuler
