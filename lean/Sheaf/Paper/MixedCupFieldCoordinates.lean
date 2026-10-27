module

public import Sheaf.Paper.PodMixedSupportCupProduct
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Paper.AdmissibleCupCoefficientPassages
public import Sheaf.Paper.MixedCupRingedNormalization
public import Sheaf.Paper.BasicOperationsCoefficientReduction

/-! # Coefficient comparisons for the mixed-support cup

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
def-pod-mixed-support-cup-product, final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-field-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings
namespace WeilConjectures.MixedCupCoefficientChange
open scoped WeilConjectures.MixedCupCoefficientChange

variable {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)

/-- Full integral coefficients on the point have the displayed field localization.
The object isomorphism is the size-equivalence counit already used by the fibre.
Source: proof step 7 (blueprint: def-sf-mixed-cup-field-coordinates). -/
def localizationPoint (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (M : sfIntegralConstructibleCategory C.l (FieldAt C F) (Spec (.of D.k))) :
    (pointChange C (.localization F)).obj
        ((pointFibreIntegralAmbient D C.l (FieldAt C F)).obj M.obj) ≅
      (pointFibreModuleLift (FieldAt C F)).mapDerivedCategory.obj
        ((pointRationalFibre D C.l C.different (FieldAt C F)).obj
          ((sfRationalConstructibleLocalization C.l (FieldAt C F) (Spec (.of D.k))).obj M)).obj :=
  (exactScalar (pointIntegralToField C.l (FieldAt C F))).app _ ≪≫
    (pointRationalLargeNormalization D C.l C.different (FieldAt C F)
      ((sfRationalConstructibleLocalization C.l (FieldAt C F) (Spec (.of D.k))).obj M)).symm

/-- The point fibre on the raw rational stage in the fixed coefficient universe.
Source: proof step 7 (blueprint: def-sf-mixed-cup-field-coordinates). -/
def rationalFibre (F : Padic.FiniteCoefficientFields C.l C.Qbar) :=
  pointRationalFibre D C.l C.different (FieldAt C F) ⋙
    (DerivedCategory.pointFiniteDimensional (FieldAt C F)).ι ⋙
    (pointFibreModuleLift (FieldAt C F)).mapDerivedCategory

/-- The point fibre on the actual common-stage category.
Source: proof step 7 (blueprint: def-sf-mixed-cup-field-coordinates). -/
def closedFibre := pointQbarFibre D C.l C.different C.Qbar ⋙
  DerivedCategory.pointFdQbarRealization C.l C.Qbar ⋙
    (pointFibreModuleLift C.Qbar).mapDerivedCategory

/-- The recorded rationalization comparison, selecting the same support choice
on both sides. Source: proof step 4
(blueprint: def-sf-mixed-cup-field-coordinates). -/
def localizationOperation (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (H : SixFunctorHigherOperations D C (FieldAt C F))
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) (compact : Bool) :
    (if compact then H.integral.support (sixFunctorStructure X) c
      else H.integral.direct (sixFunctorStructure X)) ⋙
        sfRationalConstructibleLocalization C.l (FieldAt C F) (Spec (.of D.k)) ≅
    sfRationalConstructibleLocalization C.l (FieldAt C F) X.obj.left ⋙
      (if compact then H.rational.support (sixFunctorStructure X) c
        else H.rational.direct (sixFunctorStructure X)) :=
  match compact with
  | true => (H.rationalization.supportAdjunction (sixFunctorStructure X) c).left
  | false => (H.rationalization.directAdjunction (sixFunctorStructure X)).right

/-- Localization comparisons are precisely the recorded operation comparisons
followed by the specified point-fibre normalization.
Source: proof steps 4 and 7 (blueprint: def-sf-mixed-cup-field-coordinates). -/
def LocalizationCohomologyNormalized (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left)
    (uc : ∀ {a b : Stage C} (f : Passage C a b) (compact : Bool),
      cohomology C S X c compact a ⋙ pointChange C f ≅
        change C X f ⋙ cohomology C S X c compact b) : Prop :=
  ∀ (F : Padic.FiniteCoefficientFields C.l C.Qbar) (compact : Bool)
    (K : (domain C X.obj.left (.integral F)).FullSubcategory),
    (uc (.localization F) compact).hom.app K =
      (localizationPoint C F
        ((if compact then (S F 0).higher.integral.support (sixFunctorStructure X) c
          else (S F 0).higher.integral.direct (sixFunctorStructure X)).obj K.obj)).hom ≫
        (rationalFibre C F).map
          ((localizationOperation C F (S F 0).higher X c compact).hom.app K.obj)

/-- The integral realizations of two normalized operation data have their canonical
comparison. Support uses the literal chosen-value equality; direct image uses its
specified ambient realization. No isomorphism between unrelated objects is chosen.
Source: proof steps 3--4 (blueprint: def-sf-mixed-cup-field-coordinates). -/
def integralOperationBridge (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (H H' : SixFunctorHigherOperations D C (FieldAt C F))
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) (compact : Bool)
    (K : sfIntegralConstructibleCategory C.l (FieldAt C F) X.obj.left) :
    ((if compact then H.integral.support (sixFunctorStructure X) c
      else H.integral.direct (sixFunctorStructure X)).obj K) ≅
    ((if compact then H'.integral.support (sixFunctorStructure X) c
      else H'.integral.direct (sixFunctorStructure X)).obj K) := by
  letI : LocallyOfFiniteType (sixFunctorStructure X).hom.left := X.property.1
  letI : QuasiCompact (sixFunctorStructure X).hom.left := X.property.2
  letI : IsSeparated (sixFunctorStructure X).hom.left :=
    inferInstanceAs (IsSeparated X.obj.hom)
  cases compact
  · exact (sfIntegralConstructible C.l (FieldAt C F) (Spec (.of D.k))).fullyFaithfulι.preimageIso
      (((H.integralDirectImage (sixFunctorStructure X)).app K) ≪≫
        ((H'.integralDirectImage (sixFunctorStructure X)).symm.app K))
  · exact eqToIso
      (((H.supportConstruction (sixFunctorStructure X)
          (PurCompactSupport.coefficientPrimeUnit C.l D C.different) c).choose_spec.2.2.1 K).trans
        (((H'.supportConstruction (sixFunctorStructure X)
          (PurCompactSupport.coefficientPrimeUnit C.l D C.different) c).choose_spec.2.2.1 K).symm))

/-- Comparison of independent normalized rational data through their integral
models and the recorded rationalization comparisons.
Source: proof step 4 (blueprint: def-sf-mixed-cup-field-coordinates). -/
def rationalOperationBridge (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (H H' : SixFunctorHigherOperations D C (FieldAt C F))
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) (compact : Bool)
    (K : sfRationalConstructibleCategory C.l (FieldAt C F) X.obj.left) :
    ((if compact then H.rational.support (sixFunctorStructure X) c
      else H.rational.direct (sixFunctorStructure X)).obj K) ≅
    ((if compact then H'.rational.support (sixFunctorStructure X) c
      else H'.rational.direct (sixFunctorStructure X)).obj K) :=
  ((localizationOperation C F H X c compact).symm.app K.obj) ≪≫
  (sfRationalConstructibleLocalization C.l (FieldAt C F) (Spec (.of D.k))).mapIso
    (integralOperationBridge C F H H' X c compact K.obj) ≪≫
  ((localizationOperation C F H' X c compact).app K.obj)

/-- The finite-field point scalar comparison, conjugated by the carrier lift.
Source: proof step 7 (blueprint: def-sf-mixed-cup-field-coordinates). -/
def rationalPoint (F G : Padic.FiniteCoefficientFields C.l C.Qbar) (h : F ≤ G)
    (M : sfRationalConstructibleCategory C.l (FieldAt C F) (Spec (.of D.k))) :=
  (exactScalar (RingHom.ulift.{u + 1, u + 1}
    (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar F G h).toRingHom)).app
      ((rationalFibre C F).obj M) ≪≫
  (carrierScalar (FieldAt C F) (FieldAt C G)
    (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar F G h).toRingHom).app
      ((pointRationalFibre D C.l C.different (FieldAt C F)).obj M).obj ≪≫
  (pointFibreModuleLift (FieldAt C G)).mapDerivedCategory.mapIso
    ((DerivedCategory.pointFiniteDimensional (FieldAt C G)).ι.mapIso
      ((pointRationalFibreScalarIso D C.l C.different (FieldAt C F) (FieldAt C G)
        (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar F G h)).symm.app M))

/-- The recorded point-fibre object equation after common-stage realization.
Source: proof step 7 (blueprint: def-sf-mixed-cup-field-coordinates). -/
def closurePointObject (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (M : sfRationalConstructibleCategory C.l (FieldAt C F) (Spec (.of D.k))) :=
  (DerivedCategory.pointFdQbarRealization C.l C.Qbar).mapIso
    (eqToIso ((pointQbarFibre_existsUnique D C.l C.different C.Qbar).exists.choose_spec.1
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := Spec (.of D.k)) F).obj M))).symm

/-- The point scalar tower through the actual finite subfield and its Shrink model.
Source: proof step 7 (blueprint: def-sf-mixed-cup-field-coordinates). -/
def closurePointTower (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (M : sfRationalConstructibleCategory C.l (FieldAt C F) (Spec (.of D.k))) :=
  ((DerivedCategory.fieldScalarTower
    (Shrink.algEquiv ℚ_[C.l] F.val).toRingHom F.val.subtype).symm.app
      ((pointRationalFibre D C.l C.different (FieldAt C F)).obj M).obj) ≪≫
    closurePointObject C F M

/-- Common-stage point cohomology uses the fixed scalar tower through Shrink.
The final equality is the recorded object formula of pointQbarFibre.
Source: proof step 7 (blueprint: def-sf-mixed-cup-field-coordinates). -/
def closurePoint (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (M : sfRationalConstructibleCategory C.l (FieldAt C F) (Spec (.of D.k))) :
    (pointChange C (.closure F)).obj ((rationalFibre C F).obj M) ≅
      (closedFibre C).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := Spec (.of D.k)) F).obj M) :=
  (exactScalar (RingHom.ulift.{u + 1, u + 1}
    (pointTensorStageEmbedding C.l C.Qbar F))).app _ ≪≫
  (carrierScalar (FieldAt C F) C.Qbar (pointTensorStageEmbedding C.l C.Qbar F)).app
    ((pointRationalFibre D C.l C.different (FieldAt C F)).obj M).obj ≪≫
  (pointFibreModuleLift C.Qbar).mapDerivedCategory.mapIso (closurePointTower C F M)


/-- The chosen common-stage datum's finite rational operations, with the recorded
coefficient transition and common-stage comparisons.
Source: proof step 4 (blueprint: def-sf-mixed-cup-field-coordinates). -/
abbrev commonOperations (S : Operations C) :=
  (S (Padic.finiteCoefficientBase C.l C.Qbar) 0).closure

end WeilConjectures.MixedCupCoefficientChange
