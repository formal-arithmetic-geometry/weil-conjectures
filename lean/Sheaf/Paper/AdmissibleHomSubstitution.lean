/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import Sheaf.Paper.DerivedAutomorphismHomEvaluation
public import Sheaf.Paper.DlLocallyConstructibleAdicHeart
import Sheaf.Paper.IntegralConstructibleInternalHom
import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.HomComplexShiftLeft
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.Paper.CoefficientRingedTensorHomModel

/-! # Substitution in the actual internal Hom without six-functor axioms

Source: current blueprint, fix-cor-verdier-exchange proof Steps 2--3;
Stacks Project, Tags 0A8X, 08J7, 08J9 and 0A98
(blueprint: lem-sf-admissible-hom-substitution).

The output categories remain ambient. In particular the construction of substitution
uses neither preservation of finite Tor amplitude by direct image nor biduality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b c d e v a' b'
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdmissibleHomSubstitution

/-- The displayed contravariant composite, with its actual output category.
Source: blueprint proof Step 2 (blueprint: lem-sf-admissible-hom-substitution). -/
def imageHom {A : Type a} [Category.{b} A] {B : Type c} [Category.{d} B]
    (H : Aᵒᵖ × A ⥤ A) (R : A ⥤ B) (U : A) : Aᵒᵖ ⥤ B :=
  (Functor.curry.obj H).flip.obj U ⋙ R

/-- Substitution is the functorial image of the target isomorphism, with no choice
of an inverse. Source: blueprint proof Step 2
(blueprint: lem-sf-admissible-hom-substitution). -/
def substitution {A : Type a} [Category.{b} A] {B : Type c} [Category.{d} B]
    (H : Aᵒᵖ × A ⥤ A) (R : A ⥤ B) {U V : A} (c : U ≅ V) :
    imageHom H R U ≅ imageHom H R V :=
  Functor.isoWhiskerRight ((Functor.curry.obj H).flip.mapIso c) R

/-- Signed comparison after applying the actual direct image. The input comparison
is oriented as the published signed Hom reindexing; its inverse has the orientation
in the node. Source: Stacks 0A8X, blueprint proof Step 3
(blueprint: lem-sf-admissible-hom-substitution). -/
def signedImageShift {A : Type a} [Category.{b} A] [HasShift A ℤ]
    {B : Type c} [Category.{d} B] [HasShift B ℤ]
    (H : Aᵒᵖ × A ⥤ A) (R : A ⥤ B) [R.CommShift ℤ]
    (t : ∀ (M : A) (r : ℤ),
      (Prod.sectR (op M) A ⋙ H) ⋙ shiftFunctor A (-r) ≅
        Prod.sectR (op (M⟦r⟧)) A ⋙ H)
    (M U : A) (r : ℤ) :
    (imageHom H R U).obj (op (M⟦r⟧)) ≅
      ((imageHom H R U).obj (op M))⟦-r⟧ :=
  R.mapIso ((t M r).symm.app U) ≪≫
    (R.commShiftIso (-r)).app (H.obj (op M, U))

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : Type u) [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E]

/-- The finite source-shift map is the published signed ringed-site comparison,
with coefficient exponent m+1. Source: Stacks 0A8X
(blueprint: lem-sf-admissible-hom-substitution). -/
def finiteShift {X Y : SixFunctorSpace D} (f : X ⟶ Y) (m : ℕ)
    (M U : proEtaleDerivedCategory X.obj.left
      (Padic.coefficientExtensionRing C.l E (m + 1))) (r : ℤ) :=
  signedImageShift (finiteIntrinsicDerivedInternalHom C.l E X.obj.left m)
    (proEtaleConstantDerivedDirectImage f.hom.left
      (Padic.coefficientExtensionRing C.l E (m + 1)))
    (RingedHomUniverses.sourceShift (ProEt.topology X.obj.left)
      (integralCoefficientCommRingSheaf C.l E X.obj.left m)) M U r

/-- Completed ambient source-shift comparison, followed by the completed ordinary
right-derived direct-image comparison. Source: blueprint proof Step 3
(blueprint: lem-sf-admissible-hom-substitution). -/
def integralShift {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (M U : DerivedCategory (scalarReductionSource.{u, u} C.l E X.obj.left)) (r : ℤ) :=
  signedImageShift (integralDerivedInternalHom C.l E X.obj.left)
    (sfCompletedDerivedDirectImage C.l E f.hom.left)
    (RingedHomUniverses.sourceShift (ProEt.topology X.obj.left)
      (completedIntegralCommRingSheafUnrestricted C.l E X.obj.left)) M U r

/-- The rationalized Hom has its recorded domain on every pair of bounded
constructible objects in the present geometric setting. This is a well-definedness
interface, not an added assumption on the input objects.
Source: cor-coef-integral-internal-hom and blueprint field conventions
(blueprint: lem-sf-admissible-hom-substitution).

Proof: the underlying integral objects are bounded constructible and complete.
Apply integral constructible internal Hom; its first conclusion is exactly the
pair predicate. Rationalization changes arrows and leaves these objects unchanged. -/
theorem rationalPairPermitted (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (M U : sfRationalConstructibleCategory C.l E X.obj.left) :
    constructibleRationalHomPairs C.l E X.obj.left (op M, U) := by
  sorry

/-- Actual rational internal Hom, using the recorded partial functor and its full
geometric object domain. Source: blueprint rational convention
(blueprint: lem-sf-admissible-hom-substitution). -/
def rationalHom (X : SixFunctorSpace D) [IsSeparated X.obj.hom] :
    (sfRationalConstructibleCategory C.l E X.obj.left)ᵒᵖ ×
      sfRationalConstructibleCategory C.l E X.obj.left ⥤
        sfRationalConstructibleCategory C.l E X.obj.left :=
  (constructibleRationalHomPairs C.l E X.obj.left).lift (𝟭 _)
    (fun P ↦ rationalPairPermitted D C E X P.1.unop P.2) ⋙
      rationalDerivedInternalHom C.l E X.obj.left

/-- Every common-stage pair is permitted: move its entries to their coefficient
compositum and use the integral constructible Hom theorem there.
Source: blueprint common-stage convention
(blueprint: lem-sf-admissible-hom-substitution).

Proof: the definition of commonStageHomPairs tests precisely the rational pair
at the compositum. Apply rationalPairPermitted with that finite coefficient field.
No detection of integral equality by reductions is used. -/
theorem commonPairPermitted (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (M U : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left) :
    commonStageHomPairs C.l C.Qbar X.obj.left (op M, U) := by
  sorry

/-- Actual common-stage internal Hom, retaining the published representative
comparisons and arrow action. Source: blueprint common-stage convention
(blueprint: lem-sf-admissible-hom-substitution). -/
def commonHom (X : SixFunctorSpace D) [IsSeparated X.obj.hom] :
    (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)ᵒᵖ ×
      generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left ⥤
        generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left :=
  (commonStageHomPairs C.l C.Qbar X.obj.left).lift (𝟭 _)
    (fun P ↦ commonPairPermitted D C X P.1.unop P.2) ⋙
      commonStageDerivedInternalHom C.l C.Qbar X.obj.left



/-- Completed integral Hom on all constructible pairs in this geometric setting.
Source: cor-coef-integral-internal-hom, blueprint Step 2
(blueprint: lem-sf-admissible-hom-substitution). -/
def integralHom (X : SixFunctorSpace D) [IsSeparated X.obj.hom] :
    (sfIntegralConstructibleCategory C.l E X.obj.left)ᵒᵖ ×
      sfIntegralConstructibleCategory C.l E X.obj.left ⥤
        sfIntegralConstructibleCategory C.l E X.obj.left :=
  (constructibleIntegralHomPairs C.l E X.obj.left).lift (𝟭 _)
    (fun P ↦ rationalPairPermitted D C E X ⟨P.1.unop⟩ ⟨P.2⟩) ⋙
      constructibleIntegralHom C.l E X.obj.left

/-- Lift the normalized completed comparison through the fully faithful inclusion.
The endpoints use the operation datum's actual ordinary direct image.
Source: blueprint Step 3 (blueprint: lem-sf-admissible-hom-substitution). -/
def integralConstructibleShift (S : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] (f : X ⟶ Y)
    (M U : sfIntegralConstructibleCategory C.l E X.obj.left) (r : ℤ) :
    (imageHom (integralHom D C E X) (S.integral.direct f) U).obj (op (M⟦r⟧)) ≅
      ((imageHom (integralHom D C E X) (S.integral.direct f) U).obj (op M))⟦-r⟧ :=
  (sfIntegralConstructible C.l E Y.obj.left).ι.preimageIso
    ((S.integralDirectImage f).app
        ((integralHom D C E X).obj (op (M⟦r⟧), U)) ≪≫
      (sfCompletedDerivedDirectImage C.l E f.hom.left).mapIso
        ((integralDerivedInternalHom C.l E X.obj.left).mapIso
          ((((sfIntegralConstructible C.l E X.obj.left).ι.commShiftIso r).app M).symm.op.prod
            (Iso.refl U.obj))) ≪≫
      integralShift D C E f M.obj U.obj r ≪≫
      (shiftFunctor _ (-r)).mapIso
        ((S.integralDirectImage f).app
          ((integralHom D C E X).obj (op M, U))).symm ≪≫
      (((sfIntegralConstructible C.l E Y.obj.left).ι.commShiftIso (-r)).app
        ((imageHom (integralHom D C E X) (S.integral.direct f) U).obj (op M))).symm)

/-- The canonical rational comparison of J with its integral model. Identity
components are required in the published unchanged-object coordinates.
Source: blueprint rational convention and ordinary-image normalization
(blueprint: lem-sf-admissible-hom-substitution).

Proof: the rational Hom functor is the prescribed bilinear extension of integral
Hom, while rational direct image is the prescribed linear extension of integral
direct image. Their composites have the same object formulas and the same maps
on every pure tensor. Thus the identity components form the natural isomorphism.
The component normalization determines it uniquely. -/
theorem rationalImageComparison_existsUnique (S : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] (f : X ⟶ Y)
    (U : sfIntegralConstructibleCategory C.l E X.obj.left) :
    ∃! q : imageHom (integralHom D C E X) (S.integral.direct f) U ⋙
        sfRationalConstructibleLocalization C.l E Y.obj.left ≅
      (sfRationalConstructibleLocalization C.l E X.obj.left).op ⋙
        imageHom (rationalHom D C E X) (S.rational.direct f)
          ((sfRationalConstructibleLocalization C.l E X.obj.left).obj U),
      ∀ M, HEq (q.hom.app M)
        (𝟙 ((sfRationalConstructibleLocalization C.l E Y.obj.left).obj
          ((imageHom (integralHom D C E X) (S.integral.direct f) U).obj M))) := by
  sorry

/-- The uniquely normalized comparison, rather than an arbitrary field realization.
Source: blueprint rational convention
(blueprint: lem-sf-admissible-hom-substitution). -/
def rationalImageComparison (S : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] (f : X ⟶ Y)
    (U : sfIntegralConstructibleCategory C.l E X.obj.left) :=
  (rationalImageComparison_existsUnique D C E S f U).exists.choose

/-- The field signed-shift family, before its normalization is imposed.
Source: blueprint Step 3 (blueprint: lem-sf-admissible-hom-substitution). -/
def ImageShifts {A : Type a} [Category.{b} A] [HasShift A ℤ]
    {B : Type c} [Category.{d} B] [HasShift B ℤ]
    (H : Aᵒᵖ × A ⥤ A) (R : A ⥤ B) :=
  ∀ (M U : A) (r : ℤ),
    (imageHom H R U).obj (op (M⟦r⟧)) ≅ ((imageHom H R U).obj (op M))⟦-r⟧

/-- The rational shift is precisely the localization of the completed comparison,
with the actual localization shift and J comparison inserted at both endpoints.
Source: blueprint Step 3 (blueprint: lem-sf-admissible-hom-substitution). -/
def RationalShiftNormalization (S : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] (f : X ⟶ Y)
    (s : ImageShifts (rationalHom D C E X) (S.rational.direct f)) : Prop :=
  ∀ (M U : sfIntegralConstructibleCategory C.l E X.obj.left) (r : ℤ),
    (sfRationalConstructibleLocalization C.l E Y.obj.left).map
        (integralConstructibleShift D C E S f M U r).hom ≫
      ((sfRationalConstructibleLocalization C.l E Y.obj.left).commShiftIso (-r)).hom.app
        ((imageHom (integralHom D C E X) (S.integral.direct f) U).obj (op M)) ≫
      ((rationalImageComparison D C E S f U).hom.app (op M))⟦-r⟧' =
    (rationalImageComparison D C E S f U).hom.app (op (M⟦r⟧)) ≫
      (imageHom (rationalHom D C E X) (S.rational.direct f)
        ((sfRationalConstructibleLocalization C.l E X.obj.left).obj U)).map
        (((sfRationalConstructibleLocalization C.l E X.obj.left).commShiftIso r).inv.app M).op ≫
      (s ((sfRationalConstructibleLocalization C.l E X.obj.left).obj M)
        ((sfRationalConstructibleLocalization C.l E X.obj.left).obj U) r).hom

/-- The rational signed family exists and is uniquely fixed on every unchanged
integral object, including all rational arrows with denominators.
Source: blueprint Step 3 (blueprint: lem-sf-admissible-hom-substitution).

Proof: conjugate the localization of the completed signed comparison by the
specified endpoint isomorphisms in RationalShiftNormalization. Every rational
object is an unchanged integral object, so this constructs every component and
proves uniqueness. Naturality on integral arrows descends by linearity to pure
tensors, and hence to arbitrary sums of pure tensors. -/
theorem rationalShifts_existsUnique (S : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] (f : X ⟶ Y) :
    ∃! s : ImageShifts (rationalHom D C E X) (S.rational.direct f),
      RationalShiftNormalization D C E S f s := by
  sorry

/-- The normalized rational source-shift comparison.
Source: blueprint Step 3 (blueprint: lem-sf-admissible-hom-substitution). -/
def rationalShifts (S : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] (f : X ⟶ Y) :=
  (rationalShifts_existsUnique D C E S f).exists.choose



/-- A pair included from a single finite coefficient field in the actual pair
category. Source: common-stage convention
(blueprint: lem-sf-admissible-hom-substitution). -/
def includedHomPair (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (M U : sfRationalConstructibleCategory C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X.obj.left) :
    (commonStageHomPairs C.l C.Qbar X.obj.left).FullSubcategory :=
  ⟨(op ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F).obj M),
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F).obj U),
    commonPairPermitted D C X _ _⟩

/-- The self-compositum of a coefficient field is contained in that field.
Source: the common-stage normalization
(blueprint: lem-sf-admissible-hom-substitution).

Proof: the compositum field is the supremum of F with itself; both inclusions
into F are reflexivity. This also covers the smallest coefficient field. -/
theorem includedHomBound (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (M U : sfRationalConstructibleCategory C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X.obj.left) :
    (commonStageHomObject C.l C.Qbar X.obj.left (includedHomPair D C X F M U)).stage ≤ F := by
  sorry

/-- The canonical inclusion-Hom comparison, formed from the recorded common-stage
Hom comparison and the normalized scalar identity at F. No freely chosen Hom
comparison occurs. Source: common-stage convention, blueprint proof Step 3
(blueprint: lem-sf-admissible-hom-substitution). -/
def inclusionHom (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (M U : sfRationalConstructibleCategory C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X.obj.left) :
    (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F).obj
        ((rationalHom D C
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X).obj (op M, U)) ≅
      (commonHom D C X).obj
        (op ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F).obj M),
          (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F).obj U) :=
  ((eqToIso ((commonStageDerivedInternalHom_existsUnique C.l C.Qbar
        X.obj.left).exists.choose_spec.1 (includedHomPair D C X F M U))) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left).isoToStage
      (commonStageHomObject C.l C.Qbar X.obj.left (includedHomPair D C X F M U))
        (includedHomBound D C X F M U) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F).mapIso
      (commonStageHomComparison C.l C.Qbar X.obj.left (includedHomPair D C X F M U)
          F (includedHomBound D C X F M U) ≪≫
        (rationalDerivedInternalHom C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X.obj.left).mapIso
          (ObjectProperty.isoMk (constructibleRationalHomPairs C.l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X.obj.left)
            (X := commonStageHomPairAtStage C.l C.Qbar X.obj.left
              (includedHomPair D C X F M U) F (includedHomBound D C X F M U))
            (Y := ⟨(op M, U), rationalPairPermitted D C
              (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X M U⟩)
            (Iso.prod
            ((((operationStageTransitionIso C.l C.Qbar X.obj.left F F le_rfl) ≪≫
              GeneralAlgebraicallyClosedCoefficients.unitor C.l C.Qbar X.obj.left F).app
                M).symm.op)
            (((operationStageTransitionIso C.l C.Qbar X.obj.left F F le_rfl) ≪≫
              GeneralAlgebraicallyClosedCoefficients.unitor C.l C.Qbar X.obj.left F).app
                U))))).symm

/-- The comparison of J with every finite-stage realization, including the exact
Hom scalar-unit comparisons at repeated fields.
Source: blueprint Step 3 and the common-stage direct-image comparison
(blueprint: lem-sf-admissible-hom-substitution).

Proof: the specified direct-image comparison gives its first factor. The second
is direct image of inclusionHom. Their naturality gives a natural isomorphism.
Its displayed component formula fixes the entire isomorphism uniquely. -/
theorem commonImageComparison_existsUnique
    (S : SixFunctorCommonStages D C)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] (f : X ⟶ Y)
    (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (U : sfRationalConstructibleCategory C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X.obj.left) :
    ∃! q : imageHom
        (rationalHom D C (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X)
        ((S.coefficientStages F).rational.direct f) U ⋙
        GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) F ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F).op ⋙
        imageHom (commonHom D C X) (S.commonStage.direct f)
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F).obj U),
      ∀ M, q.hom.app (op M) =
        ((S.commonStageComparison F).directAdjunction f).right.hom.app
          ((rationalHom D C
            (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X).obj (op M, U)) ≫
          (S.commonStage.direct f).map (inclusionHom D C X F M U).hom := by
  sorry

/-- The common-stage J comparison with its specified component formula.
Source: blueprint Step 3 (blueprint: lem-sf-admissible-hom-substitution). -/
def commonImageComparison (S : SixFunctorCommonStages D C)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] (f : X ⟶ Y)
    (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (U : sfRationalConstructibleCategory C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X.obj.left) :=
  (commonImageComparison_existsUnique D C S f F U).exists.choose

/-- The algebraic-closure signed comparison is the image of the normalized
rational comparison at every finite coefficient field, with the specified
inclusion shift comparison and endpoint identifications inserted.
Source: blueprint Step 3 (blueprint: lem-sf-admissible-hom-substitution). -/
def CommonShiftNormalization (S : SixFunctorCommonStages D C)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] (f : X ⟶ Y)
    (s : ImageShifts (commonHom D C X) (S.commonStage.direct f)) : Prop :=
  ∀ (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (M U : sfRationalConstructibleCategory C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X.obj.left) (r : ℤ),
    (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) F).map
        (rationalShifts D C (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F)
          (S.coefficientStages F) f M U r).hom ≫
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) F).commShiftIso (-r)).hom.app
        ((imageHom
          (rationalHom D C (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X)
          ((S.coefficientStages F).rational.direct f) U).obj (op M)) ≫
      ((commonImageComparison D C S f F U).hom.app (op M))⟦-r⟧' =
    (commonImageComparison D C S f F U).hom.app (op (M⟦r⟧)) ≫
      (imageHom (commonHom D C X) (S.commonStage.direct f)
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F).obj U)).map
        (((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F).commShiftIso r).inv.app M).op ≫
      (s ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F).obj M)
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F).obj U) r).hom

/-- Naturality of a signed family in both Hom arguments. This fixes transport
from arbitrary pairs to their representatives over a common finite field.
Source: blueprint Step 3 (blueprint: lem-sf-admissible-hom-substitution). -/
def ImageShiftNaturality {A : Type a} [Category.{b} A] [HasShift A ℤ]
    {B : Type c} [Category.{d} B] [HasShift B ℤ]
    {H : Aᵒᵖ × A ⥤ A} {R : A ⥤ B} (s : ImageShifts H R) : Prop :=
  ∀ (M N U V : A) (g : M ⟶ N) (c : U ⟶ V) (r : ℤ),
    R.map (H.map (Prod.mkHom (g⟦r⟧').op c)) ≫ (s M V r).hom =
      (s N U r).hom ≫ (R.map (H.map (Prod.mkHom g.op c)))⟦-r⟧'

/-- Existence and uniqueness of the common-stage signed comparison.
Source: blueprint Step 3 (blueprint: lem-sf-admissible-hom-substitution).

Proof: represent the inputs at one finite field and use the rational comparison.
The prescribed scalar transports commute with the signed reindexing, since they
are scalar-linear. The common-stage cocycle cancels adjacent endpoint comparisons.
This proves independence of enlargement and of representatives. Every object and
arrow has a finite-stage representative; hence the normalization determines every
component and its naturality uniquely. -/
theorem commonShifts_existsUnique (S : SixFunctorCommonStages D C)
    (hS : SixFunctorCommonStageCoherence S)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] (f : X ⟶ Y) :
    ∃! s : ImageShifts (commonHom D C X) (S.commonStage.direct f),
      CommonShiftNormalization D C S f s ∧ ImageShiftNaturality s := by
  sorry

/-- The common-stage comparison fixed on all finite-stage representatives.
Source: blueprint Step 3 (blueprint: lem-sf-admissible-hom-substitution). -/
def commonShifts (S : SixFunctorCommonStages D C)
    (hS : SixFunctorCommonStageCoherence S)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] (f : X ⟶ Y) :=
  (commonShifts_existsUnique D C S hS f).exists.choose



/-- The four actual coefficient realizations in the node. A finite exponent is m+1.
Source: coefficient conventions (blueprint: lem-sf-admissible-hom-substitution). -/
inductive Realization where
  | finite (m : ℕ)
  | integral
  | rational
  | closure

/-- Actual categories, retaining the unbounded finite ambient category and the
completed, rationalized and common-stage realizations.
Source: blueprint Step 2 (blueprint: lem-sf-admissible-hom-substitution). -/
abbrev category (X : SixFunctorSpace D) : Realization → Type (u + 2)
  | .finite m => proEtaleDerivedCategory X.obj.left
      (Padic.coefficientExtensionRing C.l E (m + 1))
  | .integral => sfIntegralConstructibleCategory C.l E X.obj.left
  | .rational => sfRationalConstructibleCategory C.l E X.obj.left
  | .closure => generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left

/-- The existing category structures, with no replacement arrow sets.
Source: coefficient conventions (blueprint: lem-sf-admissible-hom-substitution). -/
@[reducible] instance categoryCategory (X : SixFunctorSpace D) (a : Realization) :
    Category.{u + 2} (category D C E X a) :=
  match a with
  | .finite m => inferInstanceAs (Category (proEtaleDerivedCategory X.obj.left
      (Padic.coefficientExtensionRing C.l E (m + 1))))
  | .integral => inferInstanceAs (Category (sfIntegralConstructibleCategory C.l E X.obj.left))
  | .rational => inferInstanceAs (Category (sfRationalConstructibleCategory C.l E X.obj.left))
  | .closure => inferInstanceAs
      (Category (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left))

/-- The input condition is finite-Tor constructibility, not a condition on J's output.
Source: blueprint input domains (blueprint: lem-sf-admissible-hom-substitution). -/
def domain (X : SixFunctorSpace D) : (a : Realization) →
    ObjectProperty (category D C E X a)
  | .finite m => finiteTorConstructible C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left
  | .integral => fun K ↦ finiteTorConstructibleIntegral C.l E X.obj.left K.obj
  | .rational => ⊤
  | .closure => ⊤

/-- Actual internal Hom, with completed and field definitions reused verbatim.
Source: blueprint Step 2 (blueprint: lem-sf-admissible-hom-substitution). -/
def internalHom (X : SixFunctorSpace D) [IsSeparated X.obj.hom] :
    (a : Realization) → (category D C E X a)ᵒᵖ × category D C E X a ⥤ category D C E X a
  | .finite m => finiteIntrinsicDerivedInternalHom C.l E X.obj.left m
  | .integral => integralHom D C E X
  | .rational => rationalHom D C E X
  | .closure => commonHom D C X

/-- Ordinary image in the same realization, from the operation datum only.
Source: blueprint Step 2 (blueprint: lem-sf-admissible-hom-substitution). -/
def directImage {n : ℕ} {hn : 1 ≤ n} (S : SixFunctorOperationDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    (a : Realization) → category D C E X a ⥤ category D C E Y a
  | .finite m => proEtaleConstantDerivedDirectImage f.hom.left
      (Padic.coefficientExtensionRing C.l E (m + 1))
  | .integral => S.higher.integral.direct f
  | .rational => S.higher.rational.direct f
  | .closure => S.closure.commonStage.direct f

/-- Pullback paired with that ordinary image; the finite pullback is the intrinsic
exact constant-coefficient functor.
Source: blueprint ordinary-image adjunction
(blueprint: lem-sf-admissible-hom-substitution). -/
def pullback {n : ℕ} {hn : 1 ≤ n} (S : SixFunctorOperationDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    (a : Realization) → category D C E Y a ⥤ category D C E X a
  | .finite m => finiteDerivedPullback C.l E m f.hom.left
  | .integral => S.higher.integral.pull f
  | .rational => S.higher.rational.pull f
  | .closure => S.closure.commonStage.pull f

/-- The existing ordinary pullback/image adjunction at each realization.
Source: blueprint ordinary-image convention
(blueprint: lem-sf-admissible-hom-substitution). -/
def imageAdjunction {n : ℕ} {hn : 1 ≤ n} (S : SixFunctorOperationDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    (a : Realization) → pullback D C E S f a ⊣ directImage D C E S f a
  | .finite m =>
      letI := Padic.finite_coefficientExtensionRing C.l E (m + 1)
        (Nat.succ_le_succ (Nat.zero_le m))
      (sfIntrinsicConstantModuleAdjunction f.hom.left
        (Padic.coefficientExtensionRing C.l E (m + 1))).mapDerivedCategoryRightDerivedAdjunction
  | .integral => S.higher.integral.pullDirectAdjunction f
  | .rational => S.higher.rational.pullDirectAdjunction f
  | .closure => S.closure.commonStage.pullDirectAdjunction f

/-- The actual tensor, including completed integral tensor rather than ordinary
uncompleted tensor.
Source: Stacks 08J9, blueprint completed convention
(blueprint: lem-sf-admissible-hom-substitution). -/
def tensor (X : SixFunctorSpace D) : (a : Realization) →
    category D C E X a × category D C E X a ⥤ category D C E X a
  | .finite m => finiteIntrinsicDerivedTensor C.l E X.obj.left m
  | .integral => @constructibleIntegralTensor C.l _ E _ _ _ X.obj.left
      (dlAdicGeometricResidueInvertible D C X.obj.left)
  | .rational => @rationalDerivedTensor C.l _ E _ _ _ X.obj.left
      (dlAdicGeometricResidueInvertible D C X.obj.left)
  | .closure => @commonStageDerivedTensor C.l _ C.Qbar _ _ _ X.obj.left
      (dlAdicGeometricResidueInvertible D C X.obj.left)

/-- Transposition in the actual closed models. The integral transpose uses the
completion unit; rational and algebraic-closure transposes have the published
scalar normalizations.
Source: Stacks 08J9 (blueprint: lem-sf-admissible-hom-substitution). -/
def transpose (X : SixFunctorSpace D) [IsSeparated X.obj.hom] :
    (a : Realization) → (L M U : category D C E X a) →
      ((tensor D C E X a).obj (L, M) ⟶ U) ≃
        (L ⟶ (internalHom D C E X a).obj (op M, U))
  | .finite m, L, M, U => (finiteIntrinsicClosed C.l E X.obj.left m).transpose L M U
  | .integral, L, M, U =>
      (@podIntegralClosed C.l _ E _ _ _ X.obj.left
        (dlAdicGeometricResidueInvertible D C X.obj.left)).transpose L
          ⟨(op M, U), rationalPairPermitted D C E X ⟨M⟩ ⟨U⟩⟩ |>.toEquiv
  | .rational, L, M, U =>
      (@podRationalClosed C.l _ E _ _ _ X.obj.left
        (dlAdicGeometricResidueInvertible D C X.obj.left)).transpose L
          ⟨(op M, U), rationalPairPermitted D C E X M U⟩ |>.toEquiv
  | .closure, L, M, U =>
      (@podCommonClosed C.l _ C.Qbar _ _ _ X.obj.left
        (dlAdicGeometricResidueInvertible D C X.obj.left)).transpose L
          ⟨(op M, U), commonPairPermitted D C X M U⟩ |>.toEquiv

/-- Evaluation in these actual coefficient models, with Hom first.
Source: Stacks 0A98 (blueprint: lem-sf-admissible-hom-substitution). -/
def evaluation (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (a : Realization) (M U : category D C E X a) :
    (tensor D C E X a).obj ((internalHom D C E X a).obj (op M, U), M) ⟶ U :=
  (transpose D C E X a _ M U).symm (𝟙 _)



/-- The inherited shift structures on the actual realizations.
Source: cohomological convention (blueprint: lem-sf-admissible-hom-substitution). -/
@[reducible] instance categoryShift (X : SixFunctorSpace D) (a : Realization) :
    HasShift (category D C E X a) ℤ :=
  match a with
  | .finite m => inferInstanceAs (HasShift (proEtaleDerivedCategory X.obj.left
      (Padic.coefficientExtensionRing C.l E (m + 1))) ℤ)
  | .integral => inferInstanceAs (HasShift (sfIntegralConstructibleCategory C.l E X.obj.left) ℤ)
  | .rational => inferInstanceAs (HasShift (sfRationalConstructibleCategory C.l E X.obj.left) ℤ)
  | .closure => inferInstanceAs
      (HasShift (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left) ℤ)

/-- The signed comparison in each stipulated realization. The finite and integral
ones descend the signed Hom family (-1)^(r*d); the field ones are fixed by the
normalizations above, at every finite coefficient field.
Source: blueprint Step 3 (blueprint: lem-sf-admissible-hom-substitution). -/
def sourceShift {n : ℕ} {hn : 1 ≤ n} (S : SixFunctorOperationDatum D C E n hn)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] (f : X ⟶ Y) :
    (a : Realization) → ImageShifts (internalHom D C E X a) (directImage D C E S f a)
  | .finite m => finiteShift D C E f m
  | .integral => integralConstructibleShift D C E S.higher f
  | .rational => rationalShifts D C E S.higher f
  | .closure => commonShifts D C S.closure S.commonStageCoherence f

/-- Naturality, inverse components and the signed source-shift equation for the
actual operation datum, without any axiomatized six-functor hypothesis.

Source: current blueprint fix-cor-verdier-exchange proof Steps 2--3;
Stacks 0A8X, 08J7, 08JA (blueprint: lem-sf-admissible-hom-substitution).

Proof:
1. Apply bifunctoriality of actual internal Hom to (a,1) and (1,c), and then
functoriality of the actual ordinary derived image. This is naturality in M.
The components of substitution are R(H(1,c)); substitution with c inverse is
its inverse, by the two functor laws. No output-domain preservation is needed.
2. On a degree-d Hom family the signed reindexing has multiplier (-1)^(r*d).
Postcomposition by a representative of c commutes with this scalar and the
reindexing. The Hom-complex shift lemma gives its chain-isomorphism property.
Quasi-isomorphism invariance and the localization universal property descend
the natural square to all derived target maps, including inverses of quasi-isos.
3. Apply ordinary derived image and its natural shift comparison to this square.
For integral inputs the completed realization agrees with the stipulated image
by integralDirectImage and integralDirectLimitObject. All equalities are in the
completed category itself. Rationalize the same signed equality; its linear
arrow action includes denominators. At algebraic-closure coefficients represent
all entries and arrows at one common finite field. The stipulated scalar
comparisons cancel at intermediate endpoints, proving the same equation.
The operation datum only is used; no biduality or package axiom enters. -/
theorem admissible_hom_substitution {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (a : Realization) (M U V : category D C E X a)
    (hM : domain D C E X a M) (hU : domain D C E X a U)
    (hV : domain D C E X a V) (c : U ≅ V) :
    (substitution (internalHom D C E X a) (directImage D C E S f a) c).hom.app (op M) =
        (directImage D C E S f a).map
          ((internalHom D C E X a).map (Prod.mkHom (𝟙 (op M)) c.hom)) ∧
    (substitution (internalHom D C E X a) (directImage D C E S f a) c).inv.app (op M) =
        (directImage D C E S f a).map
          ((internalHom D C E X a).map (Prod.mkHom (𝟙 (op M)) c.inv)) ∧
    (∀ (N : category D C E X a), domain D C E X a N → ∀ g : N ⟶ M,
      (imageHom (internalHom D C E X a) (directImage D C E S f a) U).map g.op ≫
          (substitution (internalHom D C E X a)
            (directImage D C E S f a) c).hom.app (op N) =
        (substitution (internalHom D C E X a)
          (directImage D C E S f a) c).hom.app (op M) ≫
          (imageHom (internalHom D C E X a) (directImage D C E S f a) V).map g.op) ∧
    ∀ r : ℤ,
      (substitution (internalHom D C E X a)
          (directImage D C E S f a) c).hom.app (op (M⟦r⟧)) ≫
        (sourceShift D C E S f a M V r).hom =
      (sourceShift D C E S f a M U r).hom ≫
        ((substitution (internalHom D C E X a)
          (directImage D C E S f a) c).hom.app (op M))⟦-r⟧' := by
  sorry

section Coefficients
variable (E' : Type u) [Field E'] [Algebra (Padic C.l) E']
  [FiniteDimensional (Padic C.l) E']
  {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom]
  (a b : Realization)

/-- The internal-Hom coefficient comparison is exactly changed evaluation's
transpose. The tensor comparison has the direction tensor of images to image
of tensor, and is not required invertible.
Source: Stacks 08J9, 0A98 and blueprint coefficient paragraph
(blueprint: lem-sf-admissible-hom-substitution). -/
def homComparison (CX : category D C E X a ⥤ category D C E' X b)
    (t : CX.prod CX ⋙ tensor D C E' X b ⟶ tensor D C E X a ⋙ CX)
    (M U : category D C E X a) :
    CX.obj ((internalHom D C E X a).obj (op M, U)) ⟶
      (internalHom D C E' X b).obj (op (CX.obj M), CX.obj U) :=
  transpose D C E' X b _ _ _
    (t.app ((internalHom D C E X a).obj (op M, U), M) ≫
      CX.map (evaluation D C E X a M U))

/-- The ordinary-image coefficient comparison is the mate of the stipulated
pullback comparison, not a supplied unrelated map. Neither is required invertible.
Source: Stacks 07A7 (blueprint: lem-sf-admissible-hom-substitution). -/
def imageComparison {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}
    (S : SixFunctorOperationDatum D C E n hn)
    (S' : SixFunctorOperationDatum D C E' n' hn') (f : X ⟶ Y)
    (CX : category D C E X a ⥤ category D C E' X b)
    (CY : category D C E Y a ⥤ category D C E' Y b)
    (α : CY ⋙ pullback D C E' S' f b ⟶ pullback D C E S f a ⋙ CX) :
    directImage D C E S f a ⋙ CY ⟶ CX ⋙ directImage D C E' S' f b :=
  (mateEquiv (imageAdjunction D C E S f a) (imageAdjunction D C E' S' f b) α).natTrans

/-- The displayed sigma, made only from the transpose and the ordinary-image mate.
Source: blueprint coefficient paragraph
(blueprint: lem-sf-admissible-hom-substitution). -/
def sigma {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}
    (S : SixFunctorOperationDatum D C E n hn)
    (S' : SixFunctorOperationDatum D C E' n' hn') (f : X ⟶ Y)
    (CX : category D C E X a ⥤ category D C E' X b)
    (CY : category D C E Y a ⥤ category D C E' Y b)
    (t : CX.prod CX ⋙ tensor D C E' X b ⟶ tensor D C E X a ⋙ CX)
    (α : CY ⋙ pullback D C E' S' f b ⟶ pullback D C E S f a ⋙ CX)
    (M U : category D C E X a) (U' : category D C E' X b) (u : CX.obj U ≅ U') :
    CY.obj ((imageHom (internalHom D C E X a)
      (directImage D C E S f a) U).obj (op M)) ⟶
      (imageHom (internalHom D C E' X b)
        (directImage D C E' S' f b) U').obj (op (CX.obj M)) :=
  (imageComparison D C E E' a b S S' f CX CY α).app
      ((internalHom D C E X a).obj (op M, U)) ≫
    (directImage D C E' S' f b).map
      (homComparison D C E E' a b CX t M U ≫
        (internalHom D C E' X b).map (Prod.mkHom (𝟙 _) u.hom))

/-- The specified coefficient square in the actual four realizations, on exactly
its stated input domain. CX, CY, t and alpha denote the stipulated coefficient
functors, tensor comparison and pullback comparison; h and gamma are constructed
above and are never assumed invertible.

Source: current blueprint fix-cor-verdier-exchange proof Step 3;
Stacks 08J9, 0A98, 07A7 (blueprint: lem-sf-admissible-hom-substitution).

Proof:
4. Uncurry h_(M,V) CX(H(1,c)) and H'(1,CX(c)) h_(M,U). Tensor-comparison
naturality and evaluation naturality identify both with changed evaluation
followed by CX(c). Transposition is injective, giving their equality. This
uses no inverse of t or h. Completed transposition uses its actual completion
unit; the rational and common-stage transposes are its specified scalar images.
5. The canonical mate is a natural transformation: its factors are the whiskered
unit, stipulated pullback comparison and counit. Apply its naturality square to
H(1,c). No invertibility of this mate is needed.
6. Postcompose the equality of Step 4 by H'(1,v), use CX(c) v = u c', and apply
the target ordinary image. Paste with Step 5 and reassociate. Expanding sigma
then gives exactly the displayed equation in the target realization. At integral
coefficients this is an actual completed equality. Field functors preserve it;
common-stage composition cancels adjacent endpoint identifications. -/
theorem coefficient_square {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}
    (S : SixFunctorOperationDatum D C E n hn)
    (S' : SixFunctorOperationDatum D C E' n' hn')
    [IsSeparated Y.obj.hom] (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (CX : category D C E X a ⥤ category D C E' X b)
    (CY : category D C E Y a ⥤ category D C E' Y b)
    (t : CX.prod CX ⋙ tensor D C E' X b ⟶ tensor D C E X a ⋙ CX)
    (α : CY ⋙ pullback D C E' S' f b ⟶ pullback D C E S f a ⋙ CX)
    (M U V : category D C E X a)
    (hM : domain D C E X a M) (hU : domain D C E X a U)
    (hV : domain D C E X a V) (c : U ≅ V)
    (U' V' : category D C E' X b)
    (hU' : domain D C E' X b U') (hV' : domain D C E' X b V')
    (u : CX.obj U ≅ U') (v : CX.obj V ≅ V') (c' : U' ≅ V')
    (hc : CX.map c.hom ≫ v.hom = u.hom ≫ c'.hom) :
    CY.map ((substitution (internalHom D C E X a)
        (directImage D C E S f a) c).hom.app (op M)) ≫
      sigma D C E E' a b S S' f CX CY t α M V V' v =
    sigma D C E E' a b S S' f CX CY t α M U U' u ≫
      (substitution (internalHom D C E' X b)
        (directImage D C E' S' f b) c').hom.app (op (CX.obj M)) := by
  sorry

end Coefficients
end WeilConjectures.AdmissibleHomSubstitution
