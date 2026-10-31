/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.RightDual
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.SiteInverseImageTensor
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import all Mathlib.LinearAlgebra.Matrix.ToLin
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import all WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable

/-! # Derived dual of a dualizable sheaf in one degree

The single-degree base case of the bounded lisse duality argument, stated for any
Grothendieck monoidal coefficient category, hence also native condensed modules.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace DerivedCategory
variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]

/-- The dual of a dualizable object placed in degree `n` lies in degree `-n`.
Source: `lem-fin-lisse-field-dual`, the single-degree base case of Step 2 of
`thm-a1-curve-perverse-heart`
(blueprint: lem-per-condensed-dual-single).

Proof: represent the single object by the single cochain complex `Q`. Every term
is either the given dualizable object or zero. Choose its canonical internal dual
as right dual. The bounded-complex exact-pairing theorem pairs `Q Q` with the
termwise dual complex. Swap the pairing using the derived braiding and identify
internal Hom into the unit with the resulting left dual. The termwise dual is
supported in degree `-n`; its sole term is the internal dual of the original
object. The argument also covers the zero object.
-/
theorem nonempty_ihom_single_unit (E : A) (hE : IsDualizable E) (n : ℤ) :
    Nonempty ((ihom ((singleFunctor A n).obj E)).obj (𝟙_ _) ≅
      (singleFunctor A (-n)).obj ((ihom E).obj (𝟙_ _))) := by
  classical
  let Q := (HomologicalComplex.single A (ComplexShape.up ℤ) n).obj E
  have hc (F : A) (hF : IsDualizable F) :
      Nonempty (ExactPairing ((ihom F).obj (𝟙_ _)) F) := by
    obtain ⟨_⟩ := hF
    let : ExactPairing Fᘁ F := BraidedCategory.exactPairing_swap F Fᘁ
    exact ⟨exactPairingCongrLeft (MonoidalClosed.ihomObjUnitIso Fᘁ F)⟩
  have hl (m : ℤ) : IsDualizable (Q.X m) := by
    by_cases hm : m = n
    · subst hm
      exact hE.of_iso (HomologicalComplex.singleObjXSelf _ _ _).symm
    · exact ⟨hasRightDualOfIsZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hm)⟩
  let _ (m : ℤ) : HasRightDual (Q.X m) :=
    { rightDual := (ihom (Q.X m)).obj (𝟙_ _)
      exact := letI := (hc _ (hl m)).some
        BraidedCategory.exactPairing_swap _ _ }
  obtain ⟨_⟩ := nonempty_exactPairing_Q_obj_rightDual Q n n
  obtain ⟨_⟩ := nonempty_braidedCategory A
  let := BraidedCategory.exactPairing_swap (DerivedCategory.Q.obj Q)
    (DerivedCategory.Q.obj (CochainComplex.rightDual Q))
  let e : (singleFunctor A n).obj E ≅ DerivedCategory.Q.obj Q :=
    (singleFunctorIsoCompQ A n).app E
  obtain ⟨M, ⟨eM⟩⟩ := CochainComplex.exists_iso_single (CochainComplex.rightDual Q) (-n)
  exact ⟨((MonoidalClosed.internalHom).mapIso e.op.symm).app (𝟙_ _) ≪≫
    MonoidalClosed.ihomObjUnitIso (DerivedCategory.Q.obj (CochainComplex.rightDual Q)) _ ≪≫
    DerivedCategory.Q.mapIso eM ≪≫ ((singleFunctorIsoCompQ A (-n)).app M).symm ≪≫
    (singleFunctor A (-n)).mapIso
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-n) M).symm ≪≫
        (HomologicalComplex.eval _ _ (-n)).mapIso eM.symm ≪≫
        ((MonoidalClosed.internalHom).mapIso (HomologicalComplex.singleObjXIsoOfEq
          (ComplexShape.up ℤ) n E (-(-n)) (neg_neg n)).op).symm.app (𝟙_ _))⟩

end DerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The single-degree calculation for precisely the native lisse coefficient modules.
Source: `lem-fin-lisse-field-dual`, the single-degree base case of Step 2
(blueprint: lem-per-condensed-dual-single).

Proof: convert each normalized finite free trivialization to the raw module
inverse-image convention. Local freeness makes the original module dualizable.
Apply the general single-degree calculation above in this native module category.
-/
theorem nonempty_ihom_single_unit_of_lisse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (E : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hE : IsLisseCoefficientModule Λ E) (n : ℤ) :
    Nonempty ((ihom ((DerivedCategory.singleFunctor _ n).obj E)).obj (𝟙_ _) ≅
      (DerivedCategory.singleFunctor _ (-n)).obj ((ihom E).obj (𝟙_ _))) := by
  have hraw : IsLocallyFree (condensedRingObj Λ X) E := by
    obtain ⟨C, hC⟩ := hE
    exact ⟨C, fun i ↦ (freeAt_iff_standard Λ (C.f i) E).mpr (hC i)⟩
  exact DerivedCategory.nonempty_ihom_single_unit E hraw.isDualizable n

/-- Ordinary linear duals of native lisse modules are lisse and detect zero.
Source: the finite-free dual calculation in Step 2 of `thm-a1-curve-perverse-heart`
(blueprint: lem-per-condensed-dual-single).

Proof: normalized local freeness is equivalent to raw local freeness. Its chosen
right dual is locally free by pulling its exact pairing to each finite free
trivialization. In a braided closed category the ordinary internal dual is that
right dual. Swapping the exact pairing identifies its internal dual back with
the original module. Internal Hom out of a zero object is zero, so these two
identifications prove both directions of zero detection, including rank zero.
-/
theorem lisse_dual_properties
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (E : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hE : IsLisseCoefficientModule Λ E) :
    IsLisseCoefficientModule Λ ((ihom E).obj (𝟙_ _)) ∧
      (IsZero ((ihom E).obj (𝟙_ _)) ↔ IsZero E) := by
  have hraw : IsLocallyFree (condensedRingObj Λ X) E :=
    (isLocallyFree_iff E).mpr hE
  obtain ⟨_⟩ := hraw.isDualizable
  let : ExactPairing Eᘁ E := BraidedCategory.exactPairing_swap E Eᘁ
  let e : (ihom E).obj (𝟙_ _) ≅ Eᘁ := MonoidalClosed.ihomObjUnitIso Eᘁ E
  have hd : IsLocallyFree (condensedRingObj Λ X) ((ihom E).obj (𝟙_ _)) :=
    IsLocallyFree.of_iso e.symm hraw.of_exactPairing
  refine ⟨(isLocallyFree_iff _).mp hd, ?_⟩
  have hz {F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)} (hF : IsZero F) : IsZero ((ihom F).obj (𝟙_ _)) := by
    rw [IsZero.iff_id_eq_zero]
    apply MonoidalClosed.uncurry_injective
    have ht : IsZero (F ⊗ (ihom F).obj (𝟙_ _)) := by
      rw [IsZero.iff_id_eq_zero, ← id_whiskerRight, hF.eq_of_src (𝟙 F) 0,
        MonoidalPreadditive.zero_whiskerRight]
    exact ht.eq_of_src _ _
  constructor
  · intro h
    let ed : (ihom ((ihom E).obj (𝟙_ _))).obj (𝟙_ _) ≅ E :=
      ((MonoidalClosed.internalHom).mapIso e.symm.op).app (𝟙_ _) ≪≫
        MonoidalClosed.ihomObjUnitIso E Eᘁ
    exact (hz h).of_iso ed.symm
  · exact hz

end AlgebraicGeometry.ProEtale.CondensedRing
