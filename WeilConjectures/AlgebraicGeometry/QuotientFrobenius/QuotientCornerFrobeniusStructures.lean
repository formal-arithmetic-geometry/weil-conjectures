/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
public import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import WeilConjectures.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-! # Strict quotient-coefficient sites and Frobenius faces

The quotient diagram is a ringed sequence site. All derived categories localize complexes
of strict systems, before evaluating. Restriction retains the completed coefficient action.

## Main definitions

- `QuotientFrobenius.quotientRing`, `QuotientFrobenius.modules`, `QuotientFrobenius.derived`:
  the ring of finite quotient sheaves on the strict sequence site, its module systems and
  their derived category.
- `QuotientFrobenius.diagonal`: the diagonal module functor from completed coefficients.
- `QuotientFrobenius.Cube` and `QuotientFrobenius.face`: automorphism cubes of a Cartesian
  square and their Cartesian Frobenius faces.

## References

* Stacks 09A5
* Stacks 098T
* Stacks 03D3
* Stacks 03D8
* Stacks 06YY
* Stacks 03CZ
* Stacks 0D6E
* Stacks 0D6D
* Zheng 4.1
* Stacks 07A7
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.Scheme
namespace QuotientFrobenius

/-- The original small pro-etale site keeps its actual object and morphism universes. -/
instance (priority := 2000) baseSmall (T : Scheme.{t}) : EssentiallySmall.{t + 1} T.ProEt :=
  essentiallySmallSelf.{0} T.ProEt

attribute [local instance 2100] WeilConjectures.sfAbSheafify

attribute [local instance 2100] WeilConjectures.sfAbBijective

/-- Sheafification in the fixed coefficient universe of the quotient diagram site. -/
instance (priority := 2100) sequenceSheafify (T : Scheme.{t}) :
    HasSheafify (coefficientSequenceTopology (ProEt.topology T)) AddCommGrpCat.{t + 1} :=
  @SemilinearSections.abelianSheafify.{t + 1, t, t + 1} (ℕ × T.ProEt) _
    (essentiallySmallSelf.{0} _) _

/-- The coefficient-sized local bijectivity criterion on the quotient diagram site. -/
instance (priority := 2100) sequenceLocallyBijective (T : Scheme.{t}) :
    (coefficientSequenceTopology (ProEt.topology T)).WEqualsLocallyBijective
      AddCommGrpCat.{t + 1} :=
  @SemilinearSections.locallyBijective.{t + 1, t, t + 1} (ℕ × T.ProEt) _
    (essentiallySmallSelf.{0} _) _

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The actual finite quotient transitions, with index n representing exponent n+1. -/
abbrev transition (T : Scheme.{t}) (n : ℕ) :=
  (reductionCoefficientSystem T d).map (homOfLE (Nat.le_succ n)).op

/-- Q_T is the ring of finite quotient sheaves on the strict sequence site. -/
abbrev quotientRing (T : Scheme.{t}) :
    Sheaf (coefficientSequenceTopology (ProEt.topology T)) CommRingCat.{t + 1} :=
  @SemilinearSections.systemRing.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T)
    (d.finiteRing T) (transition d T)

/-- Strict semilinear quotient systems; this is not a diagram category of derived objects. -/
abbrev modules (T : Scheme.{t}) : Type (t + 2) :=
  @SemilinearSections.Systems.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T)
    (d.finiteRing T) (transition d T)

/-- The ordinary unbounded derived category on the ringed quotient diagram site. -/
abbrev derived (T : Scheme.{t}) : Type (t + 2) :=
  @SemilinearSections.DS.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T)
    (d.finiteRing T) (transition d T)

/-- Exact quotient-linear evaluation, including the positive-level convention. -/
abbrev evaluation (T : Scheme.{t}) (n : ℕ) :=
  @SemilinearSections.e.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T)
    (d.finiteRing T) (transition d T) n

/-- Base change on the vertical sequence sites, acting identically on the index. -/
abbrev siteMap {U V : Scheme.{t}} (u : U ⟶ V) :=
  (𝟭 ℕ).prod (proEtaleBaseChange u)

/-- Direct image and the quotient site have the same target section ring. -/
theorem coefficientTarget_obj {U V : Scheme.{t}} (u : U ⟶ V)
    (W : (ℕ × V.ProEt)ᵒᵖ) :
    (((proEtaleSheafDirectImage u CommRingCat.{t + 1}).obj
      (d.finiteRing U W.unop.1)).obj.obj (op W.unop.2)) =
      (quotientRing d U).obj.obj ((siteMap u).op.obj W) := by
  sorry

/-- A constant coefficient presheaf is a sheaf on the vertical sequence site. -/
theorem diagonalRing_isSheaf (T : Scheme.{t}) :
    Presheaf.IsSheaf (coefficientSequenceTopology (ProEt.topology T))
      ((CategoryTheory.Prod.snd ℕ T.ProEt).op ⋙ (d.completedRing T).obj) := by
  sorry

/-- The completed-coefficient diagonal ring on the same vertical sequence site. -/
def diagonalRing (T : Scheme.{t}) :
    Sheaf (coefficientSequenceTopology (ProEt.topology T)) CommRingCat.{t + 1} :=
  ⟨(CategoryTheory.Prod.snd ℕ T.ProEt).op ⋙ (d.completedRing T).obj,
    diagonalRing_isSheaf d T⟩

/-- Projection to the original site is continuous for vertical covers. -/
theorem diagonal_continuous (T : Scheme.{t}) :
    (CategoryTheory.Prod.snd ℕ T.ProEt).IsContinuous
      (coefficientSequenceTopology (ProEt.topology T))
      (ProEt.topology T) := by
  sorry

attribute [instance] diagonal_continuous

/-- The exact diagonal module functor, implemented by its sectionwise pullback presheaf. -/
abbrev diagonal (T : Scheme.{t}) :
    proEtaleRingModules T (d.completedRing T) ⥤
      SemilinearSections.Mod.{t + 1, t, t + 1} (coefficientSequenceTopology (ProEt.topology T))
        (diagonalRing d T) :=
  SheafOfModules.pushforward.{t + 1} (F := CategoryTheory.Prod.snd ℕ T.ProEt) (𝟙 _)

/-- Diagonal retains addition of module maps on every section. -/
theorem diagonal_additive (T : Scheme.{t}) : (diagonal d T).Additive := by
  sorry

attribute [instance] diagonal_additive

/-- Diagonal is exact, since its restriction to every slice is identity. -/
theorem diagonal_exact (T : Scheme.{t}) :
    PreservesFiniteLimits (diagonal d T) ∧ PreservesFiniteColimits (diagonal d T) := by
  sorry

/-- Left exactness of diagonal. -/
instance diagonal_limits (T : Scheme.{t}) : PreservesFiniteLimits (diagonal d T) :=
  (diagonal_exact d T).1

/-- Right exactness of diagonal. -/
instance diagonal_colimits (T : Scheme.{t}) : PreservesFiniteColimits (diagonal d T) :=
  (diagonal_exact d T).2

/-- Underived evaluation on the strict quotient module category. -/
abbrev moduleEvaluation (T : Scheme.{t}) (n : ℕ) :=
  @SemilinearSections.evaluation.{t + 1, t, t + 1} T.ProEt _
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T)
    (d.finiteRing T) (transition d T) n

/-- The finite direct-image cochain unit, before any evaluation of a resolution. -/
def finitePushUnit {U V : Scheme.{t}} (u : U ⟶ V) (n : ℕ)
    (P : CochainComplex (proEtaleRingModules U (d.finiteRing U n)) ℤ) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((proEtaleRingModuleDirectImage u (d.finiteRing V n) (d.finiteRing U n)
        (d.finiteRingIso u n)).mapHomologicalComplex (.up ℤ)).obj P) ≫
    (proEtaleRingModuleDirectImage u (d.finiteRing V n) (d.finiteRing U n)
      (d.finiteRingIso u n)).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj P) ≫
    (d.finitePush u n).map ((DerivedCategory.quotientCompQhIso _).hom.app P)

/-- Ordinary ambient tower evaluation at the paper's positive level n+1. -/
abbrev ambientModuleEvaluation (T : Scheme.{t}) (n : ℕ) :=
  reductionTowerEvaluation T (reductionModuleRing T (d.completedRing T)) n

/-- Derived ambient evaluation, using exact termwise evaluation. -/
abbrev ambientEvaluation (T : Scheme.{t}) (n : ℕ) :=
  reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n

/-- Exact restriction of the finite coefficient action to the completed coefficient action. -/
abbrev finiteRestriction (T : Scheme.{t}) (n : ℕ) :=
  reductionDerivedRestrict T (d.projection T n)

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Automorphisms of the four schemes of a Cartesian square commuting with all four edges,
forming a cube. -/
structure Cube (_sq : ChosenCartesianSquare g' f' f g) where
  FX : X ≅ X
  FY : Y ≅ Y
  FX' : X' ≅ X'
  FY' : Y' ≅ Y'
  f_comm : FX.hom ≫ f = f ≫ FY.hom
  g_comm : FY'.hom ≫ g = g ≫ FY.hom
  g'_comm : FX'.hom ≫ g' = g' ≫ FX.hom
  f'_comm : FX'.hom ≫ f' = f' ≫ FY'.hom

/-- Each commutative face with invertible horizontal edges is Cartesian. -/
theorem face_isPullback {U V : Scheme.{t}} (u : U ⟶ V) (FU : U ≅ U) (FV : V ≅ V)
    (comm : FU.hom ≫ u = u ≫ FV.hom) : IsPullback FU.hom u u FV.hom := by
  sorry

/-- The chosen Cartesian identification is the universal one for the Frobenius face. -/
def face {U V : Scheme.{t}} (u : U ⟶ V) (FU : U ≅ U) (FV : V ≅ V)
    (comm : FU.hom ≫ u = u ≫ FV.hom) :
    ChosenCartesianSquare FU.hom u u FV.hom where
  w := comm
  isoPullback := (face_isPullback u FU FV comm).isoPullback
  hom_fst := (face_isPullback u FU FV comm).isoPullback_hom_fst
  hom_snd := (face_isPullback u FU FV comm).isoPullback_hom_snd

/-- Integral beta is exactly the canonical ambient ringed exchange of the Frobenius face. -/
abbrev integralBeta {U V : Scheme.{t}} (u : U ⟶ V) (FU : U ≅ U) (FV : V ≅ V)
    (comm : FU.hom ≫ u = u ≫ FV.hom) :=
  d.integralExchange (face u FU FV comm)

end QuotientFrobenius
end AlgebraicGeometry.Scheme
