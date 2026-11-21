/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.CondensedClosedSupportAdjunction
public import WeilConjectures.AlgebraicGeometry.CondensedPullbackTensorComparison
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHomMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarModelImmersionExtension
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
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
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
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
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
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
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
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
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LfpTensorSingleSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicBoundedTriangulated
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.DetectionAb

/-!
# Operations on bounded constructible integral coefficient complexes

Constructibility uses finite constant scalar models. The tensors and the projection formula are
ambient and uncompleted.

## References

* Bhatt--Scholze, Proposition 6.8.11(3)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] DerivedCategory.TStructure.t
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The constructible-sheaf tensor calculation on an arbitrary Noetherian scheme. -/
private theorem tensor_single_noetherian
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hlfp : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (F G : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) F →
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) G →
      ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G).IsGE (-1) ∧
      ∀ n : ℤ, IsLocallyFinitelyPresented (condensedRingObj Λ Y)
        ((DerivedCategory.homologyFunctor _ n).obj
          ((DerivedCategory.singleFunctor _ 0).obj F ⊗
          (DerivedCategory.singleFunctor _ 0).obj G)))
    (X : Scheme.{u}) [IsNoetherian X]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))
    (hF : IsConstructibleModuleObject (condensedRingObj Λ X) F)
    (hG : IsConstructibleModuleObject (condensedRingObj Λ X) G) :
    boundedConstructible (condensedRingObj Λ X)
      ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G) := by
  classical
  let R := condensedRingObj Λ X
  let K := (DerivedCategory.singleFunctor _ 0).obj F ⊗
    (DerivedCategory.singleFunctor _ 0).obj G
  obtain ⟨S, hS⟩ := common_lfp_stratification hF hG
  let H (a : Fin S.n) := upperStar Λ (S.immersion a)
  have lfp (a : Fin S.n)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
      (hM : IsLocallyFinitelyPresented
        ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R).obj M)) :
      IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a)) ((H a).obj M) := by
    exact localFinitePresentation_of_iso
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (S.immersion a))).app _).symm
      (localFinitePresentation_comap _ hM)
  let e (a : Fin S.n) : (H a).leftDerivedFunctor.obj K ≅
      (DerivedCategory.singleFunctor _ 0).obj ((H a).obj F) ⊗
        (DerivedCategory.singleFunctor _ 0).obj ((H a).obj G) :=
    (Functor.Monoidal.μIso (H a).leftDerivedFunctor _ _).symm ≪≫
      tensorIso ((H a).singleFunctorCompLeftDerivedFunctorIso.app F)
        ((H a).singleFunctorCompLeftDerivedFunctorIso.app G)
  have hlocal (a : Fin S.n) :
      TopologicalSpace.NoetherianSpace (S.domain a) :=
    (S.immersion a).isEmbedding.noetherianSpace
  have hom_lfp (a : Fin S.n) (n : ℤ) :
      IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a))
        ((H a).obj ((DerivedCategory.homologyFunctor _ n).obj K)) := by
    apply localFinitePresentation_of_iso
      ((H a).leftDerivedFunctorHomologyFunctorIso n |>.app K).symm
    apply localFinitePresentation_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso (e a)).symm
    exact (hlfp (S.domain a) ((H a).obj F) ((H a).obj G)
      (lfp a F (hS a).1) (lfp a G (hS a).2)).2 n
  have detect
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
      (hM : ∀ a : Fin S.n, IsZero ((H a).obj M)) : IsZero M := by
    rw [IsZero.iff_id_eq_zero]
    apply Mod.hom_ext
    apply eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp S.immersion
    · intro x
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
      exact ⟨a, S.range_immersion a |>.symm ▸ ha⟩
    · intro a
      let e' := (Mod.extendScalarsIsoComapInv
        (condensedPullbackHom Λ (S.immersion a))).app
        (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R).obj M)
      have hz := (Mod.forget _).map_isZero ((hM a).of_iso e'.symm)
      change IsZero ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj M.X) at hz
      simpa using hz.eq_of_src
        ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).map (𝟙 M.X)) 0
  have hupper := DerivedCategory.isLE_tensor
    ((DerivedCategory.singleFunctor _ 0).obj F)
    ((DerivedCategory.singleFunctor _ 0).obj G) 0 0
  rw [add_zero] at hupper
  apply (mem_boundedConstructible_iff R K).2
  constructor
  · refine ⟨-1, 0, fun n hn ↦ ?_⟩
    rcases hn with hn | hn
    · apply detect
      intro a
      have hb := (hlfp (S.domain a) ((H a).obj F) ((H a).obj G)
        (lfp a F (hS a).1) (lfp a G (hS a).2)).1
      have hz := (DerivedCategory.isGE_iff _ (-1)).1 hb n hn
      exact hz.of_iso
        (((H a).leftDerivedFunctorHomologyFunctorIso n).app K ≪≫
          (DerivedCategory.homologyFunctor _ n).mapIso (e a))
    · exact (DerivedCategory.isLE_iff K 0).1 hupper n hn
  · intro n
    refine ⟨S, fun a ↦ ?_⟩
    apply localFinitePresentation_of_comap (inv (condensedPullbackHom Λ (S.immersion a)))
    apply localFinitePresentation_of_iso
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (S.immersion a))).app _)
    exact hom_lfp a n

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek supportPullback
attribute [local irreducible] closedSupportProjection openSupportProjection

/-- The projection formula for a locally closed immersion `j ≫ i`, with `j` an open
immersion and `i` a closed immersion of Noetherian schemes: for arbitrary unbounded complexes
`L` on `S` and `M` on `X`, the natural isomorphism `a_! L ⊗ᴸ M ≅ a_! (L ⊗ᴸ a^* M)`, where
`a = j ≫ i` and `a_! = Ri_* ∘ j_!`. -/
noncomputable def immersionLowerShriekProjectionIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {S Z X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X]
    (j : S ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (L : DerivedCategory (supportModules Λ S))
    (M : DerivedCategory (supportModules Λ X)) :
    ((derivedTensor Λ X).obj
        ((lowerStar Λ i).rightDerivedFunctor.obj
          ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L))).obj M ≅
      (lowerStar Λ i).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj
          (((derivedTensor Λ S).obj L).obj
            ((upperStar Λ (j ≫ i)).mapDerivedCategory.obj M))) :=
  have hij : Set.range i.base = (Set.range i.openComplement.ι.base)ᶜ := by
    simp [Scheme.Hom.coe_openComplement]
  letI : PreservesFiniteColimits (lowerStar Λ i) :=
    closedSupport_lowerStarExact Λ i i.openComplement.ι hij
  let qi := (lowerStar Λ i).mapDerivedCategory
  let qj := (openImmersionLowerShriek Λ j).mapDerivedCategory
  let pi := (upperStar Λ i).mapDerivedCategory
  let ei := Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ i)
  let ej := Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ j)
  let ecomp := Functor.mapDerivedCategoryNatIso (upperStarComp Λ j i) ≪≫
    (Functor.mapDerivedCategoryCompIso (upperStar Λ i) (upperStar Λ j)).symm
  let er := (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory
  haveI : IsIso (closedSupportProjection Λ i (qj.obj L) M) :=
    (openClosedSupportProjectionFormula Λ i i.openComplement.ι hij).1 (qj.obj L) M
  haveI : IsIso (openSupportProjection Λ j L (pi.obj M)) :=
    (openClosedSupportProjectionFormula Λ j.closedComplement j
      j.range_closedComplement).2 L (pi.obj M)
  ((derivedTensor Λ X).mapIso (er.app (qj.obj L))).app M ≪≫
    asIso (closedSupportProjection Λ i (qj.obj L) M) ≪≫
    qi.mapIso (((derivedTensor Λ Z).obj (qj.obj L)).mapIso (ei.app M)) ≪≫
    qi.mapIso (asIso (openSupportProjection Λ j L (pi.obj M))).symm ≪≫
    qi.mapIso (qj.mapIso (((derivedTensor Λ S).obj L).mapIso
      (ej.app (pi.obj M) ≪≫ (ecomp.app M).symm))) ≪≫
    (er.app _).symm

/-- Inverse image, uncompleted relative derived tensor and locally closed extension by zero
preserve bounded constructibility over the integral coefficient ring. The locally closed functor
is written explicitly as open extension by zero followed by derived closed direct image; the
latter is ordinary direct image on Noetherian schemes. Finite coefficient fields are represented
inside the fixed algebraic closure, with their induced valuation and ring of integers.

This theorem records clauses (1)--(3). Clause (4), the projection formula for arbitrary
unbounded complexes, is the natural isomorphism `immersionLowerShriekProjectionIso` (applied
with coefficient `Profinite.padicIntegersRingObj ℓ E.val`). -/
theorem integralModels_operations (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        (((upperStar (Profinite.padicIntegersRingObj ℓ E.val) f).mapDerivedCategory).obj K)) ∧
    (∀ (X : Scheme.{u}) [IsNoetherian X] (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X M →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).obj K).obj M)) ∧
    (∀ {S Z X : Scheme.{u}} [IsNoetherian S] [IsNoetherian Z] [IsNoetherian X]
      (j : S ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
      (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) S))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) S L →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        (((lowerStar (Profinite.padicIntegersRingObj ℓ E.val) i).rightDerivedFunctor).obj
          (((openImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E.val)
            j).mapDerivedCategory).obj L))) := by
  have hE : FiniteDimensional ℚ_[ℓ] E.val := E.property
  refine ⟨?_, ?_, ?_⟩
  · intro X Y _ _ f K hK
    let Λ := Profinite.padicIntegersRingObj ℓ E.val
    have hX := (adicConstructibilityPredicateComparison ℓ X Λ (.integral E.val)).1
    have hY := (adicConstructibilityPredicateComparison ℓ Y Λ (.integral E.val)).1
    refine ⟨(upperStar Λ f).bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
    apply (hX _).1
    exact constructible_of_iso
      (((upperStar Λ f).mapDerivedCategoryHomologyFunctorIso n).app K)
      (isConstructibleModuleObject_upperStar Λ f _ ((hY _).2 (hK.2 n)))
  · intro X _ K M hK hM
    let Λ := Profinite.padicIntegersRingObj ℓ E.val
    let P := boundedConstructible (condensedRingObj Λ X)
    have hp := (adicConstructibilityPredicateComparison ℓ X Λ (.integral E.val)).2
    rw [← hp] at hK hM ⊢
    have : P.IsTriangulated := isTriangulated_boundedConstructible_ellAdic_padicIntegers X ℓ E.val
    change P (K ⊗ M)
    apply prop_of_boundedConstructibleModule (P.inverseImage (tensorLeft K)) ?_ hM
    intro G hG
    exact prop_of_boundedConstructibleModule
      (P.inverseImage (tensorRight ((DerivedCategory.singleFunctor _ 0).obj G)))
      (fun F hF ↦ tensor_single_noetherian Λ
        (fun Y _ F G hF hG ↦ PadicIntegersRingObj.lfp_tensor_single Y ℓ E.val F G hF hG)
        X F G hF hG) hK
  · intro S Z X _ _ _ j _ i _ L hL
    let Λ := Profinite.padicIntegersRingObj ℓ E.val
    have ho : ScalarModelImmersionExtensionAssertions Λ j j.closedComplement :=
      ((scalarModelImmersionExtension ℓ j j.closedComplement
      (by simp [j.range_closedComplement])).2.2.2.1 E).1
    have hc : ScalarModelImmersionExtensionAssertions Λ i.openComplement.ι i :=
      ((scalarModelImmersionExtension ℓ i.openComplement.ι i
      (by simp [Scheme.Hom.coe_openComplement])).2.2.2.1 E).1
    have : PreservesFiniteColimits (lowerStar Λ i) := hc.2.2.2.1
    have hiZ : ObjectProperty.IsClosedUnderIsomorphisms
        (IsConstantModelConstructible Λ Z) :=
      (constantModelConstructibleFiniteTor_wellDefined Λ Z).1
    have hiX : ObjectProperty.IsClosedUnderIsomorphisms
        (IsConstantModelConstructible Λ X) :=
      (constantModelConstructibleFiniteTor_wellDefined Λ X).1
    have hJ : constantModelBoundedConstructible Λ Z
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L) := by
      refine ⟨(openImmersionLowerShriek Λ j).bounded_mapDerivedCategory_obj hL.1,
        fun n ↦ ?_⟩
      exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ Z)
        (((openImmersionLowerShriek Λ j).mapDerivedCategoryHomologyFunctorIso n).app L)
        (ho.2.2.2.2.1 _ (hL.2 n))
    have he := (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory
    refine ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso (he.app _).symm
      ((lowerStar Λ i).bounded_mapDerivedCategory_obj hJ.1), fun n ↦ ?_⟩
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      (((lowerStar Λ i).rightDerivedFunctorHomologyFunctorIso n).app _)
      (hc.2.2.2.2.2.1 _ (hJ.2 n))

end AlgebraicGeometry.ProEtale.CondensedRing
