module

public import Sheaf.Paper.CondensedOpenCounitRealizationSupport
public import Sheaf.Paper.CompactSupportCondensedRealization
public import Sheaf.Paper.CondensedTateRealization
public import Sheaf.Paper.ExceptionalRealizationNormalization
public import Sheaf.Paper.CompactSupportRealizationFactorNormalization
public import Sheaf.SixFunctors.IntegralOpenReductionComparison
public import Sheaf.Paper.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import Sheaf.Paper.IntegralCompactSupportUniformRestriction
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.SectionDerivedOpenAdjunctionNormalization
import Sheaf.Paper.SfImmersionCompletedPullbackComparison
import Sheaf.Paper.RealizationCompletedPull
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization

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
