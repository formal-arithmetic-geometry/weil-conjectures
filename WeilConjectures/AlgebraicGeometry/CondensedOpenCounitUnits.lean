/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOpenCounitRealizationSupport
public import WeilConjectures.AlgebraicGeometry.CompactSupportCondensedRealization
public import WeilConjectures.AlgebraicGeometry.CondensedTateRealization
public import WeilConjectures.AlgebraicGeometry.ExceptionalRealizationNormalization
public import WeilConjectures.AlgebraicGeometry.CompactSupportRealizationFactorNormalization
public import WeilConjectures.SixFunctors.IntegralOpenReductionComparison
public import WeilConjectures.AlgebraicGeometry.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportUniformRestriction
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.SectionDerivedOpenAdjunctionNormalization
import WeilConjectures.AlgebraicGeometry.SfImmersionCompletedPullbackComparison
import WeilConjectures.AlgebraicGeometry.RealizationCompletedPull
import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData

/-! # Unit and counit normalization support

Source: current blueprint, sec-smooth-purity, sk-thm-purity-transport, proof Steps 2--3;
agent-formulated normalization of the ordinary completed open adjunction
(blueprint: lem-pur-condensed-open-counit-realization).

## Main statements

- `condensed_open_counit_realization`: the specified counit equation and Tate-unit square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures
open CondensedERealization CompactSupportCondensedRealization
namespace WeilConjectures.CondensedOpenCounitRealization

variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

open CondensedExceptionalReconstruction

/-- The integral regular module in the actual completed-ring coordinates.
Source: blueprint purity transport, degree-zero Tate unit
(blueprint: lem-pur-condensed-open-counit-realization). -/
abbrev encodedUnit (T : Base k) :=
  SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l (Field.{u} l) T.scheme)

/-- Its ordinary coefficient/restriction unit map, the actual ring morphism on sections.
Source: blueprint purity transport, canonical restriction of coefficients
(blueprint: lem-pur-condensed-open-counit-realization). -/
def ordinaryUnitRestriction (U Y : Base k) (j : U.scheme ⟶ Y.scheme) :=
  (proEtaleRingModuleAdjunction j
    ((PurCompactSupport.completed l (Field.{u} l)).ring Y.scheme)
    ((PurCompactSupport.completed l (Field.{u} l)).ring U.scheme)
    ((PurCompactSupport.completed l (Field.{u} l)).pull j)).homEquiv _ _ |>.symm
      (SheafOfModules.unitToPushforwardObjUnit
        (F := proEtaleBaseChange j)
        ⟨Functor.whiskerRight
          (proEtaleRingDirectImageMap j
            ((PurCompactSupport.completed l (Field.{u} l)).ring Y.scheme)
            ((PurCompactSupport.completed l (Field.{u} l)).ring U.scheme)
            ((PurCompactSupport.completed l (Field.{u} l)).pull j)).hom
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩)

/-- The canonical j inverse R_Y to R_U, in degree zero, using the same exact pullback.
Source: blueprint purity transport, coefficient-unit normalization
(blueprint: lem-pur-condensed-open-counit-realization). -/
def unitRestriction (U Y : Base k) (j : U.scheme ⟶ Y.scheme) :
    (IntegralSystemRealization.ringedPull l (Field.{u} l) j).obj
        ((DerivedCategory.singleFunctor _ 0).obj (encodedUnit l k Y)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (encodedUnit l k U) :=
  ((proEtaleRingModulePullback j
      ((PurCompactSupport.completed l (Field.{u} l)).ring Y.scheme)
      ((PurCompactSupport.completed l (Field.{u} l)).ring U.scheme)
      ((PurCompactSupport.completed l (Field.{u} l)).pull j)).mapDerivedCategorySingleFunctor
        0).hom.app (encodedUnit l k Y) ≫
    (DerivedCategory.singleFunctor _ 0).map (ordinaryUnitRestriction l k U Y j)

/-- Ordinary restriction through the very same coefficient maps as scalarRealization.
Source: blueprint purity transport, coefficient multiplication
(blueprint: lem-pur-condensed-open-counit-realization). -/
abbrev ordinaryScalarRestriction (A : CoefficientData l (Field.{u} l) k) (T : Base k) :=
  Mod.comap (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme) ⋙
    CompactSupportFactorNormalization.ordinaryRestrict l (Field.{u} l) T.scheme
      (A.realization.atObject T)

/-- The actual composite scalar adjunction, retaining both original units.
Source: blueprint purity transport, degree-zero Tate normalization
(blueprint: lem-pur-condensed-open-counit-realization). -/
def scalarAdjunction (A : CoefficientData l (Field.{u} l) k) (T : Base k) :=
  (CompactSupportFactorNormalization.scalarAdjunction l (Field.{u} l) T.scheme
    (A.realization.atObject T)).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme))

/-- The exact-functor presentation of the right adjoint of scalarRealization.
Source: blueprint purity transport, degree-zero Tate normalization
(blueprint: lem-pur-condensed-open-counit-realization). -/
def scalarRestrictionModel (A : CoefficientData l (Field.{u} l) k) (T : Base k) :=
  Functor.mapDerivedCategoryCompIso
      (Mod.comap (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme))
      (CompactSupportFactorNormalization.ordinaryRestrict l (Field.{u} l) T.scheme
        (A.realization.atObject T)) ≪≫
    Functor.isoWhiskerLeft _
      ((CompactSupportFactorNormalization.ordinaryRestrict l (Field.{u} l) T.scheme
          (A.realization.atObject T)).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
        CompactSupportFactorNormalization.restrictionModel l (Field.{u} l) T.scheme
          (A.realization.atObject T))

/-- The degree-zero Tate coefficient multiplication: its ordinary transpose sends
each section to its specified coefficient image, and its derived transpose comes from that
ordinary map by the exact-functor comparison. These conditions determine the map;
no freely chosen unit isomorphism is permitted.
Source: blueprint purity transport, final paragraph; condensed Tate realization at d=0
(blueprint: lem-pur-condensed-open-counit-realization). -/
structure ScalarUnit (A : CoefficientData l (Field.{u} l) k) (T : Base k) where
  inclusion : encodedUnit l k T ⟶ (ordinaryScalarRestriction l k A T).obj
    (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) T.scheme))
  inclusion_sections : ∀ (V : T.scheme.ProEtᵒᵖ)
      (s : (encodedUnit l k T).val.obj V),
    HEq (inclusion.val.app V s)
      ((coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme).hom.app V
        ((A.realization.atObject T).sectionIso.inv.hom.app V
          (((A.realization.atObject T).integralIso.hom ≫
            (A.realization.atObject T).inclusion).hom.app V
              ((purCoefficientIso l (Field.{u} l) T.scheme).inv.hom.app V s))))
  comparison : (scalarRealization l k A T).obj
      ((DerivedCategory.singleFunctor _ 0).obj (encodedUnit l k T)) ≅
    (DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) T.scheme))
  normalized : (scalarAdjunction l k A T).homEquiv _ _ comparison.hom =
    (DerivedCategory.singleFunctor _ 0).map inclusion ≫
      ((ordinaryScalarRestriction l k A T).mapDerivedCategorySingleFunctor 0).inv.app _ ≫
      (scalarRestrictionModel l k A T).hom.app _

/-- The unit-normalization square in completed-ring section coordinates. The
coefficient encoding and scalarLattice carry it to the square for V(R). Its bottom
arrow is the inverse of the specified monoidal pullback unit, as in the node.
Source: blueprint purity transport, final paragraph
(blueprint: lem-pur-condensed-open-counit-realization). -/
def UnitNormalized (C : Models l k)
    (units : ∀ T : Base k, ScalarUnit l k C.coefficient T) : Prop :=
  ∀ (U Y : Base k) (j : U.scheme ⟶ Y.scheme) [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))],
    (scalarRealization l k C.coefficient U).map (unitRestriction l k U Y j) ≫
        (units U).comparison.hom ≫ (DerivedCategory.singleFunctorObjUnitIso _).hom =
      (scalarRestriction l k C.coefficient U Y j).hom.app _ ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) j).leftDerivedFunctor.map
          ((units Y).comparison.hom ≫ (DerivedCategory.singleFunctorObjUnitIso _).hom) ≫
        (CondensedRing.leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj l) j).hom

/-- The actual strict-system counit, identified before evaluation. The open
comparison is the inverse open-unit adjunct; reductionPull is fixed on the
ordinary quotient and K-flat representatives, not on evaluated derived arrows.
Source: blueprint purity transport, proof Steps 1 and 4--5
(blueprint: lem-pur-condensed-open-counit-realization). -/
def SystemCounitNormalized (C : Models l k) : Prop :=
  ∀ (U Y : Base k) (j : U.scheme ⟶ Y.scheme) [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))] (K : Integral l (Field.{u} l) Y.scheme),
    GeneratorReduction.inverseOrZero
        ((C.model.openReduction l (Field.{u} l) j).app
          ((IntegralSystemRealization.ringedPull l (Field.{u} l) j).obj
            ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj K.obj))) ≫
      (IntegralSystemRealization.Operations.shriek l (Field.{u} l) C.operations j).map
        ((C.model.reductionPull j).hom.app
          ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj K.obj)) ≫
      (C.operations.extension j).adj.counit.app _ =
    (IntegralSystemRealization.calculus l (Field.{u} l) Y.scheme).reduction.map
      ((IntegralSystemRealization.ringedOpenAdj l (Field.{u} l) j).counit.app
        ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj K.obj)) ∧
  ∀ (U Y : Base k) (j : U.scheme ⟶ Y.scheme) [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))] (K : Integral l (Field.{u} l) Y.scheme),
    (IntegralSystemRealization.calculus l (Field.{u} l) Y.scheme).adjunction.unit.app
        ((IntegralSystemRealization.ringedOpen l (Field.{u} l) j).obj
          ((IntegralSystemRealization.ringedPull l (Field.{u} l) j).obj
            ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj K.obj))) ≫
      (coefficientSequenceLimit l (Field.{u} l) Y.scheme).map
        (GeneratorReduction.inverseOrZero
          ((C.model.openReduction l (Field.{u} l) j).app _)) ≫
      (coefficientSequenceLimit l (Field.{u} l) Y.scheme).map
        ((IntegralSystemRealization.Operations.shriek l (Field.{u} l) C.operations j).map
          ((C.model.reductionPull j).hom.app
            ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj K.obj))) ≫
      (coefficientSequenceLimit l (Field.{u} l) Y.scheme).map
        ((C.operations.extension j).adj.counit.app _) ≫
      GeneratorReduction.inverseOrZero
        ((IntegralSystemRealization.calculus l (Field.{u} l) Y.scheme).adjunction.unit.app
          ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj K.obj)) =
      (IntegralSystemRealization.ringedOpenAdj l (Field.{u} l) j).counit.app
        ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj K.obj)

/-- The bundled base-preserving map has the same underlying open immersion.
Source: blueprint purity transport, geometric setting
(blueprint: lem-pur-condensed-open-counit-realization). -/
instance baseMapOpen (U Y : Base k) (j : U.scheme ⟶ Y.scheme) [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))] : IsOpenImmersion (Base.map U Y j).left :=
  inferInstanceAs (IsOpenImmersion j)

/-- The equality of the prescribed counits, read in the ambient category through
its fully faithful constructible inclusion. Both integral and condensed counits
are the actual restricted ordinary adjunction counits.
Source: blueprint purity transport, displayed open-counit equation
(blueprint: lem-pur-condensed-open-counit-realization). -/
def CounitNormalized (C : Models l k) (U Y : Base k) (j : U.scheme ⟶ Y.scheme)
    [IsOpenImmersion j] [j.IsOver (Spec (.of k))] (h : Preserves l k U Y j) : Prop :=
  ∀ K : Integral l (Field.{u} l) Y.scheme,
    extensionComparison l k C U Y j h ((restriction l k h).obj K) ≫
      (CondensedRing.openImmersionLowerShriek
        (Profinite.padicAlgClRingObj l) j).mapDerivedCategory.map
          (restrictionComparison l k C.coefficient U Y j h K).hom ≫
      ((CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj l) l (Base.map U Y j)).counit.app
          ((realization l k C.coefficient.realization Y).obj K)).hom =
      ((realization l k C.coefficient.realization Y).map
        ((restrictedAdjunction l k h).counit.app K)).hom



end WeilConjectures.CondensedOpenCounitRealization
