/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
public import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible
public import WeilConjectures.AlgebraicGeometry.ContinuousRational.DirectImage.RationalDirectImageRealization
public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalDerivedRealization
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryCompletedIntegralPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients

/-! # Proper adjunction comparison for native continuous coefficients

Source: Bhatt--Scholze, Proposition 6.8.14, Remark 6.8.15 and Lemma 6.7.2;
agent assembly of the normalized common-stage comparison
(blueprint: def-sf-native-proper-coefficient-operations).

All functors below take values in ordinary module derived categories. The comparison
is fixed before rationalization by balanced tensor multiplication, and its direct-image
comparison is fixed by the actual adjunctions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
set_option linter.all false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper
open AdicQbarRealization
attribute [local irreducible] ContinuousRational.modulePull ContinuousRational.derivedPull
  ordinaryIntegralModulePull ordinaryIntegralDerivedPull
variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (p : X ⟶ Y)
  (R : LocallyFiniteAdicRealization.Realization l X)
  (S : LocallyFiniteAdicRealization.Realization l Y)

/-- The actual ambient module operations and their canonical adjunctions. The
coefficient map is characterized by precomposition of native functions; the
ordinary adjunction by insertion of one, and the derived adjunction by its
transpose on cochain representatives and the universal resolution maps.
Source: BS 6.8.15; Stacks 03D7, 07A6 and 09T5
(blueprint: def-sf-native-proper-coefficient-operations). -/
structure Operations where
  coefficient : (adicTowerInverseImage p).obj (ring l Y S) ⟶ ring l X R
  functions : ∀ (V : Y.ProEtᵒᵖ) (s : (ring l Y S).obj.obj V)
      (x : ((proEtaleBaseChange p).obj V.unop).left),
    (((proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _
      coefficient).hom.app V s).down.1 x = s.down.1 ((pullback.fst V.unop.hom p).base x)
  [additive : (ContinuousRational.modulePull p coefficient).Additive]
  moduleAdjunction : ContinuousRational.modulePull p coefficient ⊣
    ContinuousRational.DirectImage.modulePush p coefficient
  unit_sections : ∀ (M : modules l Y S) (V : Y.ProEt) (m : M.val.obj (op V)),
    (moduleAdjunction.unit.app M).val.app (op V) m =
      ContinuousRational.moduleUnit p coefficient M V m
  pullCounit : DerivedCategory.Q ⋙ ContinuousRational.derivedPull p coefficient ⟶
    (ContinuousRational.modulePull p coefficient).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q
  pull_normalized : ContinuousRational.IsNormalizedPullCounit p coefficient pullCounit
  adjunction : ContinuousRational.derivedPull p coefficient ⊣
    ContinuousRational.DirectImage.derivedPush p coefficient
  transpose : ∀ (P : CochainComplex (modules l Y S) ℤ)
      (I : CochainComplex (modules l X R) ℤ)
      (t : ((ContinuousRational.modulePull p coefficient).mapHomologicalComplex (.up ℤ)).obj
        P ⟶ I),
    adjunction.homEquiv _ _ (pullCounit.app P ≫ DerivedCategory.Q.map t) =
      DerivedCategory.Q.map
        ((moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I t) ≫
          ContinuousRational.DirectImage.pushUnit p coefficient I

attribute [instance] Operations.additive

/-- The finite-field integral scalar comparison, fixed on the actual unit sections
and on derived cochain computation maps. Its completion is the published
ordinary-to-completed quotient-tower unit, including the zero shifted coordinate.
Source: BS 6.8.14--6.8.15, 6.6.11 and 6.5.9
(blueprint: def-sf-native-proper-coefficient-operations). -/
structure IntegralComparison (O : Operations l p R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) where
  balance : ordinaryIntegralModulePull l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p ⋙
        pbcExtend (coefficientMap l X R E) ≅
    pbcExtend (coefficientMap l Y S E) ⋙ ContinuousRational.modulePull p O.coefficient
  sections : ∀ (M : integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y)
      (V : Y.ProEt) (m : M.val.obj (op V)),
    (balance.hom.app M).val.app (op ((proEtaleBaseChange p).obj V))
      (pbcTensorSection (coefficientMap l X R E)
        ((ordinaryIntegralModulePull l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p).obj M)
        (op ((proEtaleBaseChange p).obj V)) 1
        (((ordinaryIntegralModuleAdjunction l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p).unit.app
            M).val.app (op V) m)) =
      ContinuousRational.moduleUnit p O.coefficient
        ((pbcExtend (coefficientMap l Y S E)).obj M) V
        (pbcTensorSection (coefficientMap l Y S E) M (op V) 1 m)
  derived : ordinaryIntegralDerivedPull l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p ⋙
        pbcDerivedExtend (coefficientMap l X R E) ≅
    pbcDerivedExtend (coefficientMap l Y S E) ⋙ ContinuousRational.derivedPull p O.coefficient
  representative : ∀ P : CochainComplex (integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y) ℤ,
    derived.hom.app (DerivedCategory.Q.obj P) ≫
      (ContinuousRational.derivedPull p O.coefficient).map
        (pbcComplexCounit (coefficientMap l Y S E) P) ≫
      O.pullCounit.app ((integralComplex l Y S E).obj P) =
    (pbcDerivedExtend (coefficientMap l X R E)).map
        (ordinaryIntegralPullComplexCounit l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p P) ≫
      pbcComplexCounit (coefficientMap l X R E)
        ((ordinaryIntegralPullComplex l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex balance (.up ℤ)).hom.app P)
  completion : ∀ K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y,
    (ordinaryIntegralDerivedPull l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p).obj K.obj ≅
    (integralDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p).obj K.obj
  completion_hom : ∀ K, (completion K).hom = (ordinaryIntegralCompletionComparison l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p).app K.obj

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

attribute [local irreducible] ScalarLocalization.composition ScalarLocalization.transportHom
  ScalarLocalization.category in
/-- Agreement with the specified balanced finite-integral comparison after the two
literal raw-localization object transports. The inverse completion map occurs
before ordinary scalar base change, exactly as in the statement's proof.
Source: BS 6.8.14--6.8.15
(blueprint: def-sf-native-proper-coefficient-operations). -/
def IntegralAgreement (O : Operations l p R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (I : IntegralComparison l p R S O E)
    (a : commonStageDerivedPullback l (PadicAlgCl l) p ⋙ ordinary l X R ≅
      ordinary l Y S ⋙ ContinuousRational.derivedPull p O.coefficient) : Prop :=
  ∀ K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y,
    let Q := sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y
    let J := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := Y) E
    let J' := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E
    let e : (commonStageDerivedPullback l (PadicAlgCl l) p).obj (J.obj (Q.obj K)) ≅
        J'.obj ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p).obj
          (Q.obj K)) := eqToIso ((commonStageDerivedPullback_existsUnique l (PadicAlgCl l)
      p).exists.choose_spec.1 (J.obj (Q.obj K)))
    let f : (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p).obj (Q.obj K) ≅
      (sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
        ((constructibleIntegralPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p).obj K) :=
      eqToIso ((rationalDerivedPullback_existsUnique l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
      p).exists.choose_spec.2.1 (Q.obj K))
    HEq (a.hom.app (J.obj (Q.obj K)))
      ((ordinary l X R).map e.hom ≫ (ordinary l X R).map (J'.map f.hom) ≫
        (R.integral E).hom.app
          ((constructibleIntegralPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p).obj K) ≫
        (pbcDerivedExtend (coefficientMap l X R E)).map (I.completion K).inv ≫
        I.derived.hom.app K.obj ≫
        (ContinuousRational.derivedPull p O.coefficient).map ((S.integral E).inv.app K))

end WeilConjectures.AdicQbarRealization.Proper
