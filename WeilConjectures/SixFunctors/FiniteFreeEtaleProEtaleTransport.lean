/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.DualityPairing
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.FiniteDualitySiteComparison
public import WeilConjectures.AlgebraicGeometry.EtaleLocallyClosedShriek
public import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleScalarMate
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.FixedFiniteExceptionalAt
public import WeilConjectures.AlgebraicGeometry.BoundedSiteAdjunctionTranspose

public import WeilConjectures.SixFunctors.CoefDualizingSiteMates
public import WeilConjectures.SixFunctors.EtaleHomComparisonModels
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficientComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ProEtaleExtensionZero
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionWellDefined
public import WeilConjectures.CategoryTheory.DerivedTensorRightExact
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.WitnessCompatibility


/-! # Transport of finite coefficient maps

Source: blueprint, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, paragraphs 1--3.
(blueprint: lem-sf-finite-free-etale-proetale-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor
open AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.FiniteFreeSiteTransport
open CoefDualizingSiteMates

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

/-- Total inverse, used only where the theorem asserts invertibility.
Source: blueprint finite-free proof, inverse projection comparisons
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def inverse {C : Type v} [Category.{w} C] [Preadditive C]
    {K L : C} (g : K ⟶ L) : L ⟶ K :=
  open Classical in if h : IsIso g then @inv _ _ _ _ g h else 0

/-- The ordinary exceptional adjoint at the retained compactification.
Source: blueprint finite-free proof, exceptional counit
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
abbrev exceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Et.{u} A Y ⥤ Et.{u} A X :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  (F.{u} A c).rightAdjoint

/-- The actual adjunction fixing the preceding functor and its counit.
Source: blueprint finite-free proof, exceptional counit
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def exceptionalAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    F.{u} A c ⊣ exceptional A c :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  Adjunction.ofIsLeftAdjoint (F.{u} A c)

/-- The scalar adjunction with the unchanged small pro-etale site universe.
Source: Stacks 07A6 (blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def scalarAdjunction (a : A →+* B) (X : Scheme.{u}) :
    TP.{u} a X ⊣
      @Sheaf.derivedRestrictScalars.{u} X.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
        A B inferInstance inferInstance a :=
  letI := @pbcRestriction_isRightAdjoint.{u} X.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
    A B inferInstance inferInstance a
  Adjunction.ofIsRightAdjoint
    (@Sheaf.derivedRestrictScalars.{u} X.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
      A B inferInstance inferInstance a)

/-- The pro-etale open scalar comparison is the common-right-adjoint comparison,
with the identity-on-actions restriction square. Source: Stacks 0GL1 and 07A6
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def openScalar (a : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙ TP.{u} a X ≅
      TP.{u} a U ⋙ (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  (conjugateIsoEquiv
    (((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm).comp
      (scalarAdjunction a X))
    ((scalarAdjunction a U).comp
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).symm))).symm
    (leftDerivedUpperStarRestrictScalarsIso a j) |>.symm

/-- The pro-etale proper projection mate followed by open extension by zero.
Source: blueprint finite-free proof paragraph 1; Stacks 07A6 and 0GL1
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def compactScalar (a : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : Pro.{u} A X) :
    (TP.{u} a Y).obj ((P.{u} A c).obj K) ⟶ (P.{u} B c).obj ((TP.{u} a X).obj K) :=
  finiteCoefficientChangeDirectImageMap a c.g
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K) ≫
    R(lowerStar (ModuleCat.{u + 1} B) c.g).map ((openScalar a c.i).hom.app K)

/-- The etale exceptional coefficient arrow, with the fixed compactification counit.
Source: blueprint finite-free proof, transpose of the exceptional counit
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def exceptionalScalar [Finite A] [Finite B] (a : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (M : Et.{u} A Y) :
    (Etale.scalarExtension a X).obj ((exceptional A c).obj M) ⟶
      (exceptional B c).obj ((Etale.scalarExtension a Y).obj M) :=
  (exceptionalAdjunction B c).homEquiv _ _
    (Etale.ExceptionalCoefficients.comparisonInverse a c ((exceptional A c).obj M) ≫
      (Etale.scalarExtension a Y).map ((exceptionalAdjunction A c).counit.app M))

/-- The transported counit, defined on its bounded-below domain. The zero extension
merely makes the formula total; no ambient pro-etale exceptional adjunction is asserted.
Source: blueprint finite-free proof; bounded-site counit formula
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def proCounit (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (M : Pro.{u} A Y) :
    (P.{u} A c).obj ((J.{u} A (exceptional A c)).obj M) ⟶ M :=
  open Classical in
  if h : _root_.DerivedCategory.TStructure.t.plus
      ((exceptional A c).obj ((U.{u} A Y).obj M)) then
    (compactSupportSiteComparison A c).hom.app
        ⟨(exceptional A c).obj ((U.{u} A Y).obj M), h⟩ ≫
      (S.{u} A Y).map ((exceptionalAdjunction A c).counit.app ((U.{u} A Y).obj M)) ≫
      (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app M
  else 0

/-- The defining pro-etale exceptional-counit transpose equation, in the target
coefficient category. Source: blueprint finite-free proof paragraph 1
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def IsProExceptionalScalar [Finite A] [Finite B] (a : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (M : Pro.{u} A Y)
    (b : (TP.{u} a X).obj ((J.{u} A (exceptional A c)).obj M) ⟶
      (J.{u} B (exceptional B c)).obj ((TP.{u} a Y).obj M)) : Prop :=
  (P.{u} B c).map b ≫ proCounit B c ((TP.{u} a Y).obj M) =
    inverse (compactScalar a c ((J.{u} A (exceptional A c)).obj M)) ≫
      (TP.{u} a Y).map (proCounit A c M)

/-- The specified pro-etale coefficient map is selected only from its unique
counit-transpose property, with zero away from that domain. No arbitrary map is chosen.
Source: blueprint finite-free proof paragraph 1
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def proExceptionalScalar [Finite A] [Finite B] (a : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (M : Pro.{u} A Y) :
    (TP.{u} a X).obj ((J.{u} A (exceptional A c)).obj M) ⟶
      (J.{u} B (exceptional B c)).obj ((TP.{u} a Y).obj M) :=
  open Classical in
  if h : ∃! b, IsProExceptionalScalar a c M b then h.exists.choose else 0

/-- The proved upstream K-flat instance, specialized along the algebra of the given
ring map. No preservation theorem is postponed here. Source: Stacks 06YY and 07A4
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
instance scalarKFlatInstance (a : A →+* B) (X : Scheme.{u}) :
    (sheafExtendScalars a X).PreservesKFlatQuasiIso :=
  letI := a.toAlgebra
  preservesKFlatQuasiIso_sheafExtendScalars A B X

/-- Canonical scalar identification with the K-flat left derived ordinary tensor.
Source: Stacks 06YY and 07A6 (blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def scalarDerivedIso (a : A →+* B) (X : Scheme.{u}) :
    TP.{u} a X ≅ (sheafExtendScalars a X).leftDerivedFunctor :=
  letI := a.toAlgebra
  letI := preservesKFlatQuasiIso_sheafExtendScalars A B X
  (scalarAdjunction a X).leftAdjointUniq
    ((sheafExtendScalarsAdjunction a X).derivedAdjunction.ofNatIsoRight
      ((sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1}
        a)).rightDerivedFunctorIsoMapDerivedCategory))

/-- The pro-etale scalar tensorator is uniquely fixed on flat-term K-flat models.
Source: Stacks 07A4; blueprint finite-free proof, extended evaluation
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def proScalarTensor (a : A →+* B) (X : Scheme.{u}) :
    ∀ K L : Pro.{u} A X,
      (TP.{u} a X).obj K ⊗ (TP.{u} a X).obj L ≅ (TP.{u} a X).obj (K ⊗ L) :=
  letI := a.toAlgebra
  letI := preservesKFlatQuasiIso_sheafExtendScalars A B X
  letI := (sheafExtendScalarsAdjunction a X).isLeftAdjoint
  (Functor.rightExact_tensorComparison_existsUnique (sheafExtendScalars a X)
    (TP.{u} a X) (scalarDerivedIso a X)
    (fun Q ↦ (scalarDerivedIso a X).hom.app (_root_.DerivedCategory.Q.obj Q) ≫
      (sheafExtendScalars a X).rightExact_cochainCounit Q) (fun _ ↦ rfl)).choose

/-- The etale Hom coefficient arrow is precisely the transpose of extended evaluation.
Source: blueprint finite-free proof paragraph 2; Stacks 0A5W
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def homScalarEtale (a : A →+* B) (X : Scheme.{u}) (K M : Et.{u} A X) :
    (Etale.scalarExtension a X).obj
        (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) ⟶
      ((Etale.derivedHom (ModuleCat.{u + 1} B) X).obj
        (op ((Etale.scalarExtension a X).obj K))).obj ((Etale.scalarExtension a X).obj M) :=
  (Etale.derivedTensorHomAdjunction (ModuleCat.{u + 1} B) (X := X)
    ((Etale.scalarExtension a X).obj K)).homEquiv _ _
      ((Etale.etaleHomTensorComparison X a K
        (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M)).hom ≫
        (Etale.scalarExtension a X).map
          ((Etale.derivedTensorHomAdjunction (ModuleCat.{u + 1} A) (X := X) K).counit.app M))

/-- The corresponding pro-etale Hom arrow, fixed by its own tensor-Hom adjunction.
Source: blueprint finite-free proof paragraph 2; Stacks 0A5W
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def homScalarPro (a : A →+* B) (X : Scheme.{u}) (K M : Pro.{u} A X) :
    (TP.{u} a X).obj (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) ⟶
      ((derivedHom (ModuleCat.{u + 1} B) X).obj (op ((TP.{u} a X).obj K))).obj
        ((TP.{u} a X).obj M) :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} B) (X := X) ((TP.{u} a X).obj K)).homEquiv _ _
      ((proScalarTensor a X K
        (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M)).hom ≫
        (TP.{u} a X).map
          ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A) (X := X) K).counit.app M))



/-- Constant derived unit transport induced by the degree-zero comparison.
Source: blueprint finite-free proof, dualizing endpoints
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def siteUnit (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) :
    (S.{u} A Y).obj (𝟙_ _) ⟶ (𝟙_ (Pro.{u} A Y)) :=
  CategoryTheory.finiteDualitySingleTransport
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
    (comparisonUpperStarUnitIso A Y).hom
    (_root_.DerivedCategory.singleFunctorObjUnitIso _)
    (_root_.DerivedCategory.singleFunctorObjUnitIso _)

/-- The canonical pro-etale scalar unit, using only the fixed constant-unit and
scalar/site balancing comparisons. Source: Stacks 07A6 and blueprint unit convention
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def proScalarUnit (a : A →+* B) (Y : Scheme.{u}) :
    (TP.{u} a Y).obj (𝟙_ _) ⟶ (𝟙_ (Pro.{u} B Y)) :=
  (TP.{u} a Y).map (inverse (siteUnit A Y)) ≫
    (pbcComparisonReduction.{u} Y a).hom.app (𝟙_ _) ≫
    (S.{u} B Y).map (Etale.ExceptionalCoefficients.unitIso a Y).hom ≫ siteUnit B Y

/-- The ordinary dualizing object at the fixed compactification.
Source: blueprint finite-free proof paragraph 1
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
abbrev omegaEtale (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Et.{u} A X :=
  (exceptional A c).obj (𝟙_ _)

/-- Its pro-etale transported realization, evaluated on the pro-etale unit.
Source: blueprint finite-free proof paragraph 1
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
abbrev omegaPro (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Pro.{u} A X :=
  (J.{u} A (exceptional A c)).obj (𝟙_ _)

/-- Evaluation-normalized dualizing comparison, including the comparison unit.
Source: lem-weil-finite-duality-site-comparison, fixed compactification normalization
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def omegaSite (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (S.{u} A X).obj (omegaEtale A c) ⟶ omegaPro A c :=
  alpha A (exceptional A c) (𝟙_ _) ≫
    (J.{u} A (exceptional A c)).map (siteUnit A Y)

/-- The etale dualizing counit transpose, followed by the scalar unit identification.
Source: blueprint finite-free proof paragraph 1
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def dualizingScalarEtale [Finite A] [Finite B] (a : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (Etale.scalarExtension a X).obj (omegaEtale A c) ⟶ omegaEtale B c :=
  exceptionalScalar a c (𝟙_ _) ≫
    (exceptional B c).map (Etale.ExceptionalCoefficients.unitIso a Y).hom

/-- The corresponding pro-etale dualizing counit transpose.
Source: blueprint finite-free proof paragraph 1
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def dualizingScalarPro [Finite A] [Finite B] (a : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (TP.{u} a X).obj (omegaPro A c) ⟶ omegaPro B c :=
  proExceptionalScalar a c (𝟙_ _) ≫
    (J.{u} B (exceptional B c)).map (proScalarUnit a Y)

/-- Verdier scalar map on the ordinary etale site: Hom scalar followed by u.
Source: blueprint finite-free proof paragraphs 1--2
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def verdierScalarEtale [Finite A] [Finite B] (a : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (K : Et.{u} A X) :
    (Etale.scalarExtension a X).obj (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj
      (omegaEtale A c)) ⟶
      ((Etale.derivedHom (ModuleCat.{u + 1} B) X).obj (op ((Etale.scalarExtension a X).obj
        K))).obj (omegaEtale B c) :=
  homScalarEtale a X K (omegaEtale A c) ≫
    ((Etale.derivedHom (ModuleCat.{u + 1} B) X).obj (op ((Etale.scalarExtension a X).obj
      K))).map (dualizingScalarEtale a c)

/-- The pro-etale Verdier map, formed by the identical evaluation/counit prescription.
Source: blueprint finite-free proof paragraphs 1--2
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def verdierScalarPro [Finite A] [Finite B] (a : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (K : Pro.{u} A X) :
    (TP.{u} a X).obj (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj (omegaPro A c)) ⟶
      ((derivedHom (ModuleCat.{u + 1} B) X).obj (op ((TP.{u} a X).obj K))).obj (omegaPro B c) :=
  homScalarPro a X K (omegaPro A c) ≫
    ((derivedHom (ModuleCat.{u + 1} B) X).obj (op ((TP.{u} a X).obj K))).map (dualizingScalarPro
      a c)

/-- The literal direct-image square, using the named counit-mate site map d.
Source: blueprint finite-free proof step 2
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def DirectSquare (a : A →+* B) {V X : Scheme.{u}} (f : V ⟶ X)
    (K : Et.{u} A V) : Prop :=
  IsIso ((directImageComparisonAmbient A f).app K) ∧
  IsIso ((directImageComparisonAmbient B f).app ((Etale.scalarExtension a V).obj K)) ∧
  (S.{u} B X).map (Etale.finiteCoefficientDirectImageMap a f K) ≫
      (directImageComparisonAmbient B f).app ((Etale.scalarExtension a V).obj K) =
    (pbcComparisonReduction.{u} X a).inv.app
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj K) ≫
      (TP.{u} a X).map ((directImageComparisonAmbient A f).app K) ≫
      finiteCoefficientChangeDirectImageMap a f ((S.{u} A V).obj K) ≫
      R(lowerStar (ModuleCat.{u + 1} B) f).map
        ((pbcComparisonReduction.{u} V a).hom.app K)

/-- The compact-support square, with the proper/open comparison B on both sides.
Source: blueprint finite-free proof step 3
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def CompactSquare [Finite A] [Finite B] (a : A →+* B)
    {V X : Scheme.{u}} {f : V ⟶ X} (c : Compactification f)
    (K : EtPlus.{u} A V)
    (hK : _root_.DerivedCategory.TStructure.t.plus ((Etale.scalarExtension a V).obj K.obj)) :
    Prop :=
  (S.{u} B X).map (Etale.ExceptionalCoefficients.compactSupportMap a c K.obj) =
    (pbcComparisonReduction.{u} X a).inv.app ((F.{u} A c).obj K.obj) ≫
      (TP.{u} a X).map ((compactSupportSiteComparison A c).inv.app K) ≫
      compactScalar a c ((S.{u} A V).obj K.obj) ≫
      (P.{u} B c).map ((pbcComparisonReduction.{u} V a).hom.app K.obj) ≫
      (compactSupportSiteComparison B c).hom.app
        ⟨(Etale.scalarExtension a V).obj K.obj, hK⟩

/-- The exceptional square, fixing both endpoint maps rho and the independently
specified pro-etale counit transpose. Source: blueprint finite-free proof step 4
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def ExceptionalSquare [Finite A] [Finite B] (a : A →+* B)
    {V X : Scheme.{u}} {f : V ⟶ X} (c : Compactification f) (M : Et.{u} A X) : Prop :=
  IsIso (alpha A (exceptional A c) M) ∧
    IsIso (Etale.ExceptionalCoefficients.compactSupportMap a c ((exceptional A c).obj M)) ∧
    IsIso (compactScalar a c
      ((J.{u} A (exceptional A c)).obj ((S.{u} A X).obj M))) ∧
    _root_.DerivedCategory.TStructure.t.plus
      ((exceptional A c).obj ((U.{u} A X).obj ((S.{u} A X).obj M))) ∧
    _root_.DerivedCategory.TStructure.t.plus
      ((exceptional B c).obj ((U.{u} B X).obj
        ((TP.{u} a X).obj ((S.{u} A X).obj M)))) ∧
    (∃! b, IsProExceptionalScalar a c ((S.{u} A X).obj M) b) ∧
    (S.{u} B V).map (exceptionalScalar a c M) ≫
        alpha B (exceptional B c) ((Etale.scalarExtension a X).obj M) =
      (pbcComparisonReduction.{u} V a).inv.app ((exceptional A c).obj M) ≫
        (TP.{u} a V).map (alpha A (exceptional A c) M) ≫
        proExceptionalScalar a c ((S.{u} A X).obj M) ≫
        (J.{u} B (exceptional B c)).map ((pbcComparisonReduction.{u} X a).hom.app M)

/-- The Hom square is an equality of evaluation transposes; the contravariant first
input uses the opposite scalar/site comparison. Source: blueprint finite-free proof step 5
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def HomSquare [Finite A] [Finite B] (a : A →+* B) (X : Scheme.{u})
    (K M : Et.{u} A X) : Prop :=
  IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X K M) ∧
  IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} B) X
    ((Etale.scalarExtension a X).obj K) ((Etale.scalarExtension a X).obj M)) ∧
  (S.{u} B X).map (homScalarEtale a X K M) ≫
      siteComparisonEvaluationHom (ModuleCat.{u + 1} B) X
        ((Etale.scalarExtension a X).obj K) ((Etale.scalarExtension a X).obj M) =
    (pbcComparisonReduction.{u} X a).inv.app (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj
      (op K)).obj M) ≫
      (TP.{u} a X).map (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X K M) ≫
      homScalarPro a X ((S.{u} A X).obj K) ((S.{u} A X).obj M) ≫
      (((derivedHom (ModuleCat.{u + 1} B) X).map ((pbcComparisonReduction.{u} X a).inv.app
        K).op).app
        ((TP.{u} a X).obj ((S.{u} A X).obj M))) ≫
      ((derivedHom (ModuleCat.{u + 1} B) X).obj (op ((S.{u} B X).obj ((Etale.scalarExtension a
        X).obj K)))).map
        ((pbcComparisonReduction.{u} X a).hom.app M)

/-- The normalized dualizing square. Source: blueprint finite-free proof step 4
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def DualizingSquare [Finite A] [Finite B] (a : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Prop :=
  IsIso (omegaSite A c) ∧ IsIso (omegaSite B c) ∧
    (S.{u} B X).map (dualizingScalarEtale a c) ≫ omegaSite B c =
      (pbcComparisonReduction.{u} X a).inv.app (omegaEtale A c) ≫
        (TP.{u} a X).map (omegaSite A c) ≫ dualizingScalarPro a c

/-- The normalized comparison on Verdier duals.
Source: lem-weil-finite-duality-site-comparison, evaluation normalization
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def verdierSite (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (K : Et.{u} A X) :
    (S.{u} A X).obj (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj (omegaEtale A c)) ⟶
      ((derivedHom (ModuleCat.{u + 1} A) X).obj (op ((S.{u} A X).obj K))).obj (omegaPro A c) :=
  siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X K (omegaEtale A c) ≫
    ((derivedHom (ModuleCat.{u + 1} A) X).obj (op ((S.{u} A X).obj K))).map (omegaSite A c)

/-- The Verdier square, with beta defined from v and u on each site.
Source: blueprint finite-free proof step 6
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def VerdierSquare [Finite A] [Finite B] (a : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (K : Et.{u} A X) : Prop :=
  IsIso (verdierSite A c K) ∧
    (S.{u} B X).map (verdierScalarEtale a c K) ≫
        verdierSite B c ((Etale.scalarExtension a X).obj K) =
      (pbcComparisonReduction.{u} X a).inv.app (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj
        (op K)).obj (omegaEtale A c)) ≫
        (TP.{u} a X).map (verdierSite A c K) ≫
        verdierScalarPro a c ((S.{u} A X).obj K) ≫
        ((derivedHom (ModuleCat.{u + 1} B) X).map ((pbcComparisonReduction.{u} X a).inv.app
          K).op).app
          (omegaPro B c)



/-- The closed transported counit uses the inverse named direct-image mate and
then the etale and comparison counits. Source: blueprint finite-free proof step 4
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def closedCounit (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (M : Pro.{u} A X) :
    R(lowerStar (ModuleCat.{u + 1} A) i).obj
        ((J.{u} A (Etale.etaleShriekClosedExceptional A i)).obj M) ⟶ M :=
  inverse ((directImageComparisonAmbient A i).app
      ((Etale.etaleShriekClosedExceptional A i).obj ((U.{u} A X).obj M))) ≫
    (S.{u} A X).map ((Etale.etaleShriekClosedAdjunction A i).counit.app
      ((U.{u} A X).obj M)) ≫
    (derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).counit.app M

/-- The closed exceptional coefficient transpose is specified in the S-linear
category by its counit equation. Source: blueprint finite-free proof steps 4 and 8
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def IsProClosedScalar [Finite A] [Finite B] (a : A →+* B)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (M : Pro.{u} A X)
    (b : (TP.{u} a Z).obj ((J.{u} A (Etale.etaleShriekClosedExceptional A i)).obj M) ⟶
      (J.{u} B (Etale.etaleShriekClosedExceptional B i)).obj ((TP.{u} a X).obj M)) :
    Prop :=
  R(lowerStar (ModuleCat.{u + 1} B) i).map b ≫ closedCounit B i ((TP.{u} a X).obj M) =
    inverse (finiteCoefficientChangeDirectImageMap a i
        ((J.{u} A (Etale.etaleShriekClosedExceptional A i)).obj M)) ≫
      (TP.{u} a X).map (closedCounit A i M)

/-- The closed pro-etale map is the uniquely specified counit transpose whenever
it exists. Source: blueprint finite-free proof steps 4 and 8
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def closedScalarPro [Finite A] [Finite B] (a : A →+* B)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (M : Pro.{u} A X) :
    (TP.{u} a Z).obj ((J.{u} A (Etale.etaleShriekClosedExceptional A i)).obj M) ⟶
      (J.{u} B (Etale.etaleShriekClosedExceptional B i)).obj ((TP.{u} a X).obj M) :=
  open Classical in if h : ∃! b, IsProClosedScalar a i M b then h.exists.choose else 0

/-- Equality with the named etale closed exceptional transpose, including its actual
source and target. Source: blueprint finite-free proof steps 4 and 8
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def ClosedSquare [Finite A] [Finite B] (a : A →+* B)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (M : Et.{u} A X) : Prop :=
  (∃! b, IsProClosedScalar a i ((S.{u} A X).obj M) b) ∧
    IsIso ((directImageComparisonAmbient A i).app
      ((Etale.etaleShriekClosedExceptional A i).obj
        ((U.{u} A X).obj ((S.{u} A X).obj M)))) ∧
    IsIso ((directImageComparisonAmbient B i).app
      ((Etale.etaleShriekClosedExceptional B i).obj
        ((U.{u} B X).obj ((TP.{u} a X).obj ((S.{u} A X).obj M))))) ∧
    IsIso (Etale.finiteCoefficientDirectImageMap a i
      ((Etale.etaleShriekClosedExceptional A i).obj M)) ∧
    IsIso (finiteCoefficientChangeDirectImageMap a i
      ((J.{u} A (Etale.etaleShriekClosedExceptional A i)).obj ((S.{u} A X).obj M))) ∧
    IsIso (alpha A (Etale.etaleShriekClosedExceptional A i) M) ∧
    IsIso (alpha B (Etale.etaleShriekClosedExceptional B i)
      ((Etale.scalarExtension a X).obj M)) ∧
    (S.{u} B Z).map (Etale.etaleShriekClosedCoefficientMap a i M) ≫
        alpha B (Etale.etaleShriekClosedExceptional B i)
          ((Etale.scalarExtension a X).obj M) =
      (pbcComparisonReduction.{u} Z a).inv.app
          ((Etale.etaleShriekClosedExceptional A i).obj M) ≫
        (TP.{u} a Z).map (alpha A (Etale.etaleShriekClosedExceptional A i) M) ≫
        closedScalarPro a i ((S.{u} A X).obj M) ≫
        (J.{u} B (Etale.etaleShriekClosedExceptional B i)).map
          ((pbcComparisonReduction.{u} X a).hom.app M)

/-- Composition-compatible transport of equations, with specified endpoints. This
covers counit and successive-extension words as well as individual arrows, and
reflects a mixed reduction-square equality. Source: blueprint finite-free proof steps 7--9
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def EquationTransport (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) : Prop :=
  ∀ (K L : Et.{u} A X),
    (∃ a : ℤ, K.IsGE a) → (∃ a : ℤ, L.IsGE a) →
    ∀ (K' L' : Pro.{u} A X) (eK : (S.{u} A X).obj K ≅ K')
      (eL : (S.{u} A X).obj L ≅ L') (p q : K ⟶ L),
      (eK.inv ≫ (S.{u} A X).map p ≫ eL.hom =
        eK.inv ≫ (S.{u} A X).map q ≫ eL.hom) ↔ p = q

/-- Evaluation and double-dual compatibility with the fixed dualizing comparison.
Source: blueprint finite-free proof step 6, evaluation and its transpose
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def PairingTransport (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Prop :=
  ∃ w : (S.{u} A X).obj (omegaEtale A c) ≅ omegaPro A c,
    w.hom = omegaSite A c ∧
    ∃ hEt : Etale.AmbientDualityPairing (ModuleCat.{u + 1} A) X (omegaEtale A c),
    ∃ hPro : AmbientDualityPairing (ModuleCat.{u + 1} A) X (omegaPro A c),
      ∀ K : Et.{u} A X,
        Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K →
          FiniteDualityCompatibility (ModuleCat.{u + 1} A) X
            (omegaEtale A c) (omegaPro A c) w hEt hPro K

/-- The transported exceptional counit equation, on the stated bounded etale-origin
input. Source: blueprint finite-free proof step 4
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def CounitTransport (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (M : Et.{u} A Y) : Prop :=
  ∃ h : _root_.DerivedCategory.TStructure.t.plus ((exceptional A c).obj M),
    (P.{u} A c).map (alpha A (exceptional A c) M) ≫
        proCounit A c ((S.{u} A Y).obj M) =
      (compactSupportSiteComparison A c).hom.app ⟨(exceptional A c).obj M, h⟩ ≫
        (S.{u} A Y).map ((exceptionalAdjunction A c).counit.app M)

/-- The direct-image two-step coefficient path, reassociated to the composite ring map.
Source: blueprint finite-free proof step 7
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def directPath {C : Type (u + 1)} [CommRing C] (a : A →+* B) (b : B →+* C)
    {V X : Scheme.{u}} (f : V ⟶ X) (K : Pro.{u} A V) :=
  (tensorComp a b X).inv.app (R(lowerStar (ModuleCat.{u + 1} A) f).obj K) ≫
    (TP.{u} b X).map (finiteCoefficientChangeDirectImageMap a f K) ≫
    finiteCoefficientChangeDirectImageMap b f ((TP.{u} a V).obj K) ≫
    R(lowerStar (ModuleCat.{u + 1} C) f).map ((tensorComp a b V).hom.app K)

/-- The closed-counit two-step path, with both scalar associators specified.
Source: blueprint finite-free proof steps 7--9
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def closedPath {C : Type (u + 1)} [CommRing C] [Finite A] [Finite B] [Finite C]
    (a : A →+* B) (b : B →+* C) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (M : Pro.{u} A X) :=
  (tensorComp a b Z).inv.app ((J.{u} A (Etale.etaleShriekClosedExceptional A i)).obj M) ≫
    (TP.{u} b Z).map (closedScalarPro a i M) ≫
    closedScalarPro b i ((TP.{u} a X).obj M) ≫
    (J.{u} C (Etale.etaleShriekClosedExceptional C i)).map
      ((tensorComp a b X).hom.app M)

/-- The ordinary etale closed path with the same balancing normalization.
Source: blueprint finite-free proof step 9
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def closedPathEtale {C : Type (u + 1)} [CommRing C] [Finite A] [Finite B] [Finite C]
    (a : A →+* B) (b : B →+* C) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (M : Et.{u} A X) :=
  (pbcFixedScalarExtensionComp.{u} Z.smallEtaleTopology a b (b.comp a) rfl).inv.app
      ((Etale.etaleShriekClosedExceptional A i).obj M) ≫
    (Etale.scalarExtension b Z).map (Etale.etaleShriekClosedCoefficientMap a i M) ≫
    Etale.etaleShriekClosedCoefficientMap b i ((Etale.scalarExtension a X).obj M) ≫
    (Etale.etaleShriekClosedExceptional C i).map
      ((pbcFixedScalarExtensionComp.{u} X.smallEtaleTopology a b (b.comp a) rfl).hom.app M)

/-- The two-step dualizing-counit path, normalized at the source dualizing object.
Source: blueprint finite-free proof step 7
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def dualizingPath {C : Type (u + 1)} [CommRing C] [Finite A] [Finite B] [Finite C]
    (a : A →+* B) (b : B →+* C) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :=
  (tensorComp a b X).inv.app (omegaPro A c) ≫
    (TP.{u} b X).map (dualizingScalarPro a c) ≫ dualizingScalarPro b c

/-- Two successive evaluation transposes, with the contravariant Hom endpoint
transported by the inverse scalar associator. Source: blueprint finite-free proof step 7
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def homPath {C : Type (u + 1)} [CommRing C] (a : A →+* B) (b : B →+* C)
    (X : Scheme.{u}) (K M : Pro.{u} A X) :=
  (tensorComp a b X).inv.app (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) ≫
    (TP.{u} b X).map (homScalarPro a X K M) ≫
    homScalarPro b X ((TP.{u} a X).obj K) ((TP.{u} a X).obj M) ≫
    ((derivedHom (ModuleCat.{u + 1} C) X).map
      ((tensorComp a b X).inv.app K).op).app ((TP.{u} b X).obj ((TP.{u} a X).obj M)) ≫
    ((derivedHom (ModuleCat.{u + 1} C) X).obj (op ((TP.{u} (b.comp a) X).obj K))).map
      ((tensorComp a b X).hom.app M)

/-- Two successive Verdier arrows with their specified Hom endpoint reassociation.
Source: blueprint finite-free proof step 7
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def verdierPath {C : Type (u + 1)} [CommRing C] [Finite A] [Finite B] [Finite C]
    (a : A →+* B) (b : B →+* C) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : Pro.{u} A X) :=
  (tensorComp a b X).inv.app
      (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj (omegaPro A c)) ≫
    (TP.{u} b X).map (verdierScalarPro a c K) ≫
    verdierScalarPro b c ((TP.{u} a X).obj K) ≫
    ((derivedHom (ModuleCat.{u + 1} C) X).map
      ((tensorComp a b X).inv.app K).op).app (omegaPro C c)

/-- The compact-support two-step coefficient path at the retained compactification.
Source: blueprint finite-free proof step 7
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def compactPath {C : Type (u + 1)} [CommRing C] [Finite A] [Finite B] [Finite C]
    (a : A →+* B) (b : B →+* C) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : Pro.{u} A X) :=
  (tensorComp a b Y).inv.app ((P.{u} A c).obj K) ≫
    (TP.{u} b Y).map (compactScalar a c K) ≫
    compactScalar b c ((TP.{u} a X).obj K) ≫
    (P.{u} C c).map ((tensorComp a b X).hom.app K)

/-- Actual successive-extension equations for the named pro-etale arrows on the
specified etale-origin inputs. Source: blueprint finite-free proof step 7
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def SuccessiveTransport {C : Type (u + 1)} [CommRing C]
    [Finite A] [Finite B] [Finite C] (a : A →+* B) (b : B →+* C)
    {X V Z Y : Scheme.{u}} (f : V ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ Y} (c : Compactification aX) : Prop :=
  (∀ K : Et.{u} A V,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) V K →
      directPath a b f ((S.{u} A V).obj K) =
        finiteCoefficientChangeDirectImageMap (b.comp a) f ((S.{u} A V).obj K)) ∧
  (∀ M : Et.{u} A X,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X M →
      closedPath a b i ((S.{u} A X).obj M) =
        closedScalarPro (b.comp a) i ((S.{u} A X).obj M)) ∧
  dualizingPath a b c = dualizingScalarPro (b.comp a) c ∧
  (∀ K M : Et.{u} A X,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K →
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X M →
      homPath a b X ((S.{u} A X).obj K) ((S.{u} A X).obj M) =
        homScalarPro (b.comp a) X ((S.{u} A X).obj K) ((S.{u} A X).obj M)) ∧
  (∀ K : Et.{u} A X,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K →
      verdierPath a b c ((S.{u} A X).obj K) =
        verdierScalarPro (b.comp a) c ((S.{u} A X).obj K)) ∧
  (∀ K : Et.{u} A X,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K →
      compactPath a b c ((S.{u} A X).obj K) =
        compactScalar (b.comp a) c ((S.{u} A X).obj K))

/-- The named mixed paths for a commuting coefficient square. HEq expresses only
transport along the displayed equality of composite ring maps, retaining their exact
scalar associators and Hom variances. The last equivalence explicitly reflects the
closed-square equality to the etale site. Source: blueprint finite-free proof steps 8--9
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def MixedTransport {C D : Type (u + 1)} [CommRing C] [CommRing D]
    [Finite A] [Finite B] [Finite C] [Finite D]
    (a : A →+* B) (r : B →+* D) (q : A →+* C) (b : C →+* D)
    {X V Z Y : Scheme.{u}} (f : V ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ Y} (c : Compactification aX) : Prop :=
  r.comp a = b.comp q ∧
  (∀ K : Et.{u} A V,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) V K →
      HEq (directPath a r f ((S.{u} A V).obj K))
        (directPath q b f ((S.{u} A V).obj K))) ∧
  (∀ M : Et.{u} A X,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X M →
      HEq (closedPath a r i ((S.{u} A X).obj M))
        (closedPath q b i ((S.{u} A X).obj M))) ∧
  HEq (dualizingPath a r c) (dualizingPath q b c) ∧
  (∀ K M : Et.{u} A X,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K →
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X M →
      HEq (homPath a r X ((S.{u} A X).obj K) ((S.{u} A X).obj M))
        (homPath q b X ((S.{u} A X).obj K) ((S.{u} A X).obj M))) ∧
  (∀ K : Et.{u} A X,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K →
      HEq (verdierPath a r c ((S.{u} A X).obj K))
        (verdierPath q b c ((S.{u} A X).obj K))) ∧
  (∀ K : Et.{u} A X,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K →
      HEq (compactPath a r c ((S.{u} A X).obj K))
        (compactPath q b c ((S.{u} A X).obj K))) ∧
  (∀ M : Et.{u} A X,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X M →
      (HEq (closedPath a r i ((S.{u} A X).obj M))
          (closedPath q b i ((S.{u} A X).obj M)) ↔
        HEq (closedPathEtale a r i M) (closedPathEtale q b i M)))


/-- The full named-arrow transport assertion for a coefficient map at the three
schemes, with finite-Tor constructible inputs. All constituent maps are fixed above.
Source: blueprint finite-free proof paragraphs 1--3
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def Transport [Finite A] [Finite B] (a : A →+* B)
    {X V Z Y : Scheme.{u}} (f : V ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ Y} (c : Compactification aX) : Prop :=
  (∀ K : Et.{u} A V,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) V K →
      DirectSquare a f K) ∧
  (∀ M : Et.{u} A X,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X M →
      ClosedSquare a i M) ∧
  DualizingSquare a c ∧
  ExceptionalSquare a c (𝟙_ _) ∧
  (∀ K M : Et.{u} A X,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K →
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X M →
      HomSquare a X K M) ∧
  (∀ K : Et.{u} A X,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K →
      VerdierSquare a c K) ∧
  (∀ K : EtPlus.{u} A X,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K.obj →
      ∃ hK, CompactSquare a c K hK) ∧
  EquationTransport B X ∧ EquationTransport B V ∧ EquationTransport B Z ∧
  PairingTransport A c ∧ PairingTransport B c ∧
  CounitTransport A c (𝟙_ _) ∧ CounitTransport B c (𝟙_ _) ∧
  (∀ (C : Type (u + 1)) [CommRing C] [Finite C] (b : B →+* C),
    SuccessiveTransport a b f i c) ∧
  (∀ M : Et.{u} A X,
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X M →
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} B) Z
        ((Etale.scalarExtension a Z).obj ((Etale.etaleShriekClosedExceptional A i).obj M)) ∧
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} B) Z
        ((Etale.etaleShriekClosedExceptional B i).obj ((Etale.scalarExtension a X).obj M)))



/-- The specified quotient transition, including equal positive indices.
Source: blueprint finite-free proof paragraph 3, quotient representatives
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
def quotientMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n m : ℕ) (h : m ≤ n) :
    Padic.coefficientExtensionRing l E n →+* Padic.coefficientExtensionRing l E m :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right h)

/-- The full conclusion at two actual positive coefficient levels. Finiteness is
supplied by the recorded coefficient theorem; it is not an extra assumption.
Source: blueprint finite-free proof, coefficient conventions
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def AtCoefficients (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (m : ℕ) (hm : 1 ≤ m)
    (a : Padic.coefficientExtensionRing l E n →+* Padic.coefficientExtensionRing l L m)
    {X V Z Y : Scheme.{u}} (f : V ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ Y} (c : Compactification aX) : Prop :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  letI := Padic.finite_coefficientExtensionRing l L m hm
  Transport (RingHom.ulift.{u + 1, u + 1} a) f i c

/-- The canonical ramified coefficient homomorphism, induced by the integer inclusion
on quotient representatives. This is the published quotient inclusion
`PurCompactSupport.ramifiedMap`, with the principal-ideal ramification equality
normalized to its ideal-map form; no second construction is made.
Source: blueprint finite-free proof paragraph 1
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
abbrev ramifiedMap (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (e : ℕ)
    (heq : Ideal.span
      ({WeilConjectures.integralScalarIntegerInclusion l E L ι
        (Padic.coefficientExtensionUniformizer l E)} :
          Set (Padic.coefficientExtensionIntegers l L)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l L ^ e}) (n : ℕ) :
    Padic.coefficientExtensionRing l E n →+* Padic.coefficientExtensionRing l L (e * n) :=
  WeilConjectures.PurCompactSupport.ramifiedMap l E L ι e
    (by
      change Ideal.map _ (Ideal.span {_} ^ 1) = Ideal.span {_} ^ e
      simpa only [pow_one, Ideal.map_span, Set.image_singleton,
        Ideal.span_singleton_pow] using heq) n

/-- The mixed assertion at the four actual positive quotient levels. Finiteness and
ULift only implement the established coefficient size convention.
Source: blueprint finite-free proof paragraph 3
(blueprint: lem-sf-finite-free-etale-proetale-transport). -/
@[irreducible]
def MixedAtCoefficients (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m en em : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hen : 1 ≤ en) (hem : 1 ≤ em)
    (a : Padic.coefficientExtensionRing l E n →+* Padic.coefficientExtensionRing l L en)
    (r : Padic.coefficientExtensionRing l L en →+* Padic.coefficientExtensionRing l L em)
    (q : Padic.coefficientExtensionRing l E n →+* Padic.coefficientExtensionRing l E m)
    (b : Padic.coefficientExtensionRing l E m →+* Padic.coefficientExtensionRing l L em)
    {X V Z Y : Scheme.{u}} (f : V ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ Y} (c : Compactification aX) : Prop :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  letI := Padic.finite_coefficientExtensionRing l E m hm
  letI := Padic.finite_coefficientExtensionRing l L en hen
  letI := Padic.finite_coefficientExtensionRing l L em hem
  MixedTransport (RingHom.ulift.{u + 1, u + 1} a) (RingHom.ulift.{u + 1, u + 1} r)
    (RingHom.ulift.{u + 1, u + 1} q) (RingHom.ulift.{u + 1, u + 1} b) f i c

/-- Named coefficient maps commute with exact etale/pro-etale realization at the
ramified finite-free levels and at both vertical quotients.

Source: blueprint latest, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, paragraphs 1--3
(blueprint: lem-sf-finite-free-etale-proetale-transport).

Proof: reduce an integral basis of O_L over O_E at each level. The reductions
identify B_n with a finite free A_n-module, compatibly with quotient transitions.
On flat-term K-flat representatives the scalar/site and scalar/scalar comparisons
are the balancing maps, so their cube and associator equations agree on pure tensors.
For c, transpose the two sides using the inverse-image adjunction; both are the
same extended counit after this cube. Apply the result to the proper part of a
fixed compactification. For its open part use the open-adjunction transpose of
the identity, giving the compact-support square with its prescribed normalization.
The bounded-site Hom bijection now transposes that square and the transported
counit equation, giving the exceptional square; the identity-open compactification
gives the closed case. Evaluating on the coefficient unit gives u and its specified
dualizing comparison. Transpose extended evaluation to obtain the Hom square.
Its normalization identifies both evaluation maps and their double-dual transposes;
compose it with u to obtain beta. Functoriality and the balancing associator
transport counit and successive-extension equations. Repeat with the actual
quotients (n,m) and (en,em); these arguments use derived tensor and require no
flatness of a quotient. The etale locally-closed-shriek theorem at the identity
open types both closed outputs as constructible finite-Tor. Full faithfulness of
comparison on D+ reflects equality of the two closed mixed-square composites.
All adjunction transposes used here have bounded etale-origin inputs. -/
theorem finiteFreeEtaleProEtaleTransport
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (e : ℕ) (he : 1 ≤ e)
    (heq : Ideal.span
      ({WeilConjectures.integralScalarIntegerInclusion l E L ι
        (Padic.coefficientExtensionUniformizer l E)} :
          Set (Padic.coefficientExtensionIntegers l L)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l L ^ e})
    (X V Z : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [V.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (V ↘ Spec (.of D.k))] [LocallyOfFiniteType (V ↘ Spec (.of D.k))]
    [QuasiCompact (V ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    (f : V ⟶ X) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [i.IsOver (Spec (.of D.k))] [IsClosedImmersion i]
    (c : Compactification (X ↘ Spec (.of D.k))) (n : ℕ) :
    AtCoefficients l E (n + 1) (Nat.succ_pos n)
      L (e * (n + 1)) (Nat.mul_pos he (Nat.succ_pos n)) (ramifiedMap l E L ι e heq (n + 1)) f i c ∧
    (∀ (m : ℕ) (hmn : m ≤ n),
      (quotientMap l L (e * (n + 1)) (e * (m + 1))
          (Nat.mul_le_mul_left e (Nat.add_le_add_right hmn 1))).comp
          (ramifiedMap l E L ι e heq (n + 1)) =
        (ramifiedMap l E L ι e heq (m + 1)).comp
          (quotientMap l E (n + 1) (m + 1) (Nat.add_le_add_right hmn 1)) ∧
      AtCoefficients l E (m + 1) (Nat.succ_pos m)
        L (e * (m + 1)) (Nat.mul_pos he (Nat.succ_pos m)) (ramifiedMap l E L ι e heq (m + 1)) f
          i c ∧
      AtCoefficients l E (n + 1) (Nat.succ_pos n)
        E (m + 1) (Nat.succ_pos m) (quotientMap l E (n + 1) (m + 1)
          (Nat.add_le_add_right hmn 1)) f i c ∧
      AtCoefficients l L (e * (n + 1)) (Nat.mul_pos he (Nat.succ_pos n))
        L (e * (m + 1)) (Nat.mul_pos he (Nat.succ_pos m))
        (quotientMap l L (e * (n + 1)) (e * (m + 1))
          (Nat.mul_le_mul_left e (Nat.add_le_add_right hmn 1))) f i c ∧
      MixedAtCoefficients l E L (n + 1) (m + 1) (e * (n + 1)) (e * (m + 1))
        (Nat.succ_pos n) (Nat.succ_pos m)
        (Nat.mul_pos he (Nat.succ_pos n)) (Nat.mul_pos he (Nat.succ_pos m))
        (ramifiedMap l E L ι e heq (n + 1))
        (quotientMap l L (e * (n + 1)) (e * (m + 1))
          (Nat.mul_le_mul_left e (Nat.add_le_add_right hmn 1)))
        (quotientMap l E (n + 1) (m + 1) (Nat.add_le_add_right hmn 1))
        (ramifiedMap l E L ι e heq (m + 1)) f i c) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteFreeSiteTransport
