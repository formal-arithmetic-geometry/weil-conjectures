/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.SixFunctors.FrobeniusCohomologyTransport
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.CommonStageCompactWeilCohomology
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.FrobeniusGeometricExchange
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.SixFunctors.FrobeniusPointTransport
import Sheaf.SixFunctors.FrobeniusSquareCartesian

/-!
# Degree-zero Frobenius exchange

Source: Stacks Project, Tag 07A7, remark-base-change; blueprint
`prop-cohomological-finiteness`, Proof Step 7
(blueprint: lem-pod-frobenius-exchange-degree-zero).

All degree-zero identifications below are the canonical homology comparisons.
The underived inverse-image mate is evaluated by restriction along its Cartesian
map. Equations are written using j, the inverse of lambda.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PodDegreeZero

/-- Canonical H⁰(Rf_*M) = f_*M: the unbounded-to-classical derived comparison,
followed by the left-exact right-derived-zero comparison.
Source: Stacks Tag 07A7 (blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def directZero {X Y : Scheme.{u}} (a : X ⟶ Y) (A : Type u) [CommRing A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :=
  letI : IsGrothendieckAbelian.{u + 1}
      (proEtaleRingModules X (proEtaleConstantRing X A)) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, u + 1}
      (ProEt.topology X)
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
  letI : PreservesFiniteLimits (proEtaleConstantModuleDirectImage a A) :=
    (proEtaleConstantModuleDirectImage_additive_leftExact a A).2
  (proEtaleConstantModuleDirectImage a A).homologyRightDerivedFunctorObjSingleFunctorIso M 0
    ≪≫ (proEtaleConstantModuleDirectImage a A).rightDerivedZeroIsoSelf.app M

/-- The ordinary tensor-unit comparison j, evaluated on a sheaf in degree zero.
The single-complex term identifications make this a map of the original sheaves.
Source: Stacks Tag 03D6 (blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def tensorUnit (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ)
    (M : integralOperationsFiniteModules l E Y n) :=
  (inverseImageFiniteModules l E g n).map
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).inv ≫
    (inverseImageFiniteComparisonComplex l E g n
      ((CochainComplex.singleFunctor _ 0).obj M)).f 0 ≫
    (integralOperationsLevelPullback l E g n).map
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).hom

/-- The tensor-unit map in the finite intrinsic pullback coordinates.
Source: Stacks Tags 03D6 and 00YV
(blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def intrinsicUnit (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ)
    (M : integralOperationsFiniteModules l E Y n) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  tensorUnit l E g n M ≫
    (inverseImageFiniteIntrinsicPullbackComparison g
      (Padic.coefficientExtensionRing l E (n + 1))).hom.app M

/-- The sectionwise Cartesian arrow defining the underived inverse-image mate.
Its underlying map is (y,v) ↦ (g(y),v), with no linearity over k required.
Source: Stacks Tag 07A7 and Tags 00VE, 00WX
(blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def squareArrow {X Y : Scheme.{u}} (a : X ⟶ Y) (g : X ⟶ X) (h : Y ⟶ Y)
    [IsIso g] [IsIso h] (w : g ≫ a = a ≫ h) (U : Y.ProEt) :
    (proEtaleIsoPostcompose g).obj ((proEtaleBaseChange a).obj U) ⟶
      (proEtaleBaseChange a).obj ((proEtaleIsoPostcompose h).obj U) :=
  MorphismProperty.Over.homMk
    (pullback.map U.hom a (U.hom ≫ h) a (𝟙 U.left) g h
      (Category.id_comp _).symm w.symm)
    (pullback.lift_snd _ _ _)

/-- Underlying section map of the underived mate B, obtained from its actual
Cartesian arrow and restriction. The colimit counit formula identifies precisely
this map with the transpose in the node, on every site object.
Source: Stacks Tags 00VE, 00WX (blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def underivedMate {X Y : Scheme.{u}} (a : X ⟶ Y) (g : X ⟶ X) (h : Y ⟶ Y)
    [IsIso g] [IsIso h] (w : g ≫ a = a ≫ h) (A : Type u) [CommRing A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : Y.ProEt)
    (x : M.val.obj (op ((proEtaleBaseChange a).obj
      ((proEtaleIsoPostcompose h).obj U)))) :=
  M.val.map (squareArrow a g h w U).op x

/-- H⁰ of the specified derived exchange in the canonical ordinary pullback
and direct-image coordinates. All factors are the recorded canonical comparisons.
Source: Stacks Tag 07A7 (blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def exchangeZero {X Y : Scheme.{u}} (a : X ⟶ Y) (g : X ⟶ X) (h : Y ⟶ Y)
    (w : g ≫ a = a ≫ h) (A : Type u) [CommRing A] [Finite A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :=
  (sfIntrinsicPullback A h).map (directZero a A M).inv ≫
    ((sfIntrinsicPullback A h).mapDerivedCategoryHomologyFunctorIso 0).hom.app
      ((proEtaleConstantDerivedDirectImage a A).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
    (DerivedCategory.homologyFunctor _ 0).map
      ((FrobeniusExchange.finiteExchange A a a g h w).app
        ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
    (DerivedCategory.homologyFunctor _ 0).map
      ((proEtaleConstantDerivedDirectImage a A).map
        (((sfIntrinsicPullback A g).mapDerivedCategorySingleFunctor 0).hom.app M)) ≫
    (directZero a A ((sfIntrinsicPullback A g).obj M)).hom

/-- The small derived-category model for point coefficient modules, as used by Fib_s.
Source: blueprint point-fibre size convention
(blueprint: lem-pod-frobenius-exchange-degree-zero). -/
instance pointModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

/-- H⁰ of a map of point section complexes in the canonical exact-sections coordinates.
Source: Stacks Tags 0982, 0946 (blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def sectionZero (D : FiniteFieldDatum.{u}) (A : Type u) [CommRing A]
    {N K : proEtaleDerivedCategory (Spec (.of D.k)) A}
    (f : (pointFiniteSections D.k A).mapDerivedCategory.{u + 2, u + 1}.obj N ⟶
      (pointFiniteSections D.k A).mapDerivedCategory.{u + 2, u + 1}.obj K) :=
  ((pointFiniteSections D.k A).mapDerivedCategoryHomologyFunctorIso 0).hom.app N ≫
    (DerivedCategory.homologyFunctor _ 0).map f ≫
    ((pointFiniteSections D.k A).mapDerivedCategoryHomologyFunctorIso 0).inv.app K

/-- Exact finite pullback in the intrinsic coordinates, at positive exponent n+1.
Source: Stacks Tag 03D6 (blueprint: lem-pod-frobenius-exchange-degree-zero). -/
abbrev pull (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) g

/-- The unique arrow to the final object of the small pro-etale site.
Source: Stacks Tag 098K (blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def finalRestriction {X : Scheme.{u}} (U : X.ProEt) : U ⟶ ProEt.mk (𝟙 X) :=
  MorphismProperty.Over.homMk U.hom (Category.comp_id _)

/-- Restriction along an automorphism, from (X,g) to the final object (X,id).
In the sectionwise inverse-image model this is exactly restriction, insertion,
and sheafification, not a k-linear pullback.
Source: Stacks Tag 00WX (blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def isoRestriction {X : Scheme.{u}} (g : X ⟶ X) [IsIso g] :
    (proEtaleIsoPostcompose g).obj (ProEt.mk (𝟙 X)) ⟶ ProEt.mk (𝟙 X) :=
  MorphismProperty.Over.homMk g (Category.comp_id _)

/-- The geometric Galois map has the instance carried by its prescribed automorphism.
Source: blueprint geometric Frobenius (blueprint: lem-pod-frobenius-exchange-degree-zero). -/
instance galoisIsIso (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    IsIso (FrobeniusExchange.galois D Y₀) :=
  inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

/-- The normalized degree-zero point transport on any finite derived point object.
This is the actual recorded iota, with only exact homology comparisons composed.
Source: blueprint point-transport formula and Stacks Tag 07A7
(blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def pointTransportZero (n : ℕ)
    (N : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  sectionZero D (Padic.coefficientExtensionRing l E (n + 1))
      (frobeniusPointTransportFinite D l hl E n N) ≫
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).map
      (((pull l E (frobeniusPointIso D).hom n).mapDerivedCategoryHomologyFunctorIso 0).inv.app N)

/-- The normalized degree-zero iota at Ra_*M, using H⁰(Ra_*M)=a_*M.
Source: Stacks Tag 07A7 (blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def iotaZero (n : ℕ)
    (M : integralOperationsFiniteModules l E (D.geometricFiber Y₀).left n) :=
  let A := Padic.coefficientExtensionRing l E (n + 1)
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let N := (proEtaleConstantDerivedDirectImage (D.geometricFiber Y₀).hom A).obj
    ((DerivedCategory.singleFunctor _ 0).obj M)
  (pointFiniteSections D.k A).map (directZero (D.geometricFiber Y₀).hom A M).inv ≫
    pointTransportZero D l hl E n N ≫
    (pointFiniteSections D.k A).map
      ((pull l E (frobeniusPointIso D).hom n).map
        (directZero (D.geometricFiber Y₀).hom A M).hom)

/-- The normalized H⁰ of the actual ordinary transport tau, not a redefinition by
underived sections. Its last factors identify H⁰(Ra_*Lg^*M) with a_*g^*M.
Source: blueprint ordinary cohomology transport and Stacks Tag 07A7
(blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def transportZero (n : ℕ)
    (M : integralOperationsFiniteModules l E (D.geometricFiber Y₀).left n) :=
  let A := Padic.coefficientExtensionRing l E (n + 1)
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  (pointFiniteSections D.k A).map (directZero (D.geometricFiber Y₀).hom A M).inv ≫
    sectionZero D A (frobeniusOrdinaryTransportFinite D l hl E Y₀ n
      ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
    (pointFiniteSections D.k A).map
      ((DerivedCategory.homologyFunctor _ 0).map
        ((proEtaleConstantDerivedDirectImage (D.geometricFiber Y₀).hom A).map
          (((pull l E (FrobeniusExchange.galois D Y₀) n).mapDerivedCategorySingleFunctor
            0).hom.app M)) ≫
        (directZero (D.geometricFiber Y₀).hom A
          ((pull l E (FrobeniusExchange.galois D Y₀) n).obj M)).hom)

/-- The actual Frobenius exchange expressed in ordinary degree-zero coordinates.
Source: Stacks Tag 07A7 (blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def frobeniusExchangeZero (n : ℕ)
    (M : integralOperationsFiniteModules l E (D.geometricFiber Y₀).left n) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  exchangeZero (D.geometricFiber Y₀).hom (FrobeniusExchange.galois D Y₀)
    (frobeniusPointIso D).hom
    (D.frobenius_square_cartesian Y₀ (sfWeilCohomologyPoint D)
      (frobeniusCohomologyModelMap D Y₀)).2.2.2.2.2.2.2.w
    (Padic.coefficientExtensionRing l E (n + 1)) M

/-- The underived mate, in its canonical sectionwise inverse-image coordinates.
Source: Stacks Tags 07A7 and 00WX
(blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def frobeniusUnderivedMate (n : ℕ)
    (M : integralOperationsFiniteModules l E (D.geometricFiber Y₀).left n) :=
  underivedMate (D.geometricFiber Y₀).hom (FrobeniusExchange.galois D Y₀)
    (frobeniusPointIso D).hom
    (D.frobenius_square_cartesian Y₀ (sfWeilCohomologyPoint D)
      (frobeniusCohomologyModelMap D Y₀)).2.2.2.2.2.2.2.w
    (Padic.coefficientExtensionRing l E (n + 1)) M

/-- The ordinary direct image sheaf used in the degree-zero formulas.
Source: Stacks Tag 03DA (blueprint: lem-pod-frobenius-exchange-degree-zero). -/
abbrev directSheaf (n : ℕ)
    (M : integralOperationsFiniteModules l E (D.geometricFiber Y₀).left n) :=
  (proEtaleConstantModuleDirectImage (D.geometricFiber Y₀).hom
    (Padic.coefficientExtensionRing l E (n + 1))).obj M

/-- The final-object identification of sections on Y with sections of a_*M on s.
It is restriction along the canonical projection Y ×_s s → Y.
Source: Stacks Tag 03DA (blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def toPointSections (n : ℕ)
    (M : integralOperationsFiniteModules l E (D.geometricFiber Y₀).left n)
    (x : M.val.obj (op (ProEt.mk (𝟙 (D.geometricFiber Y₀).left)))) :=
  M.val.map (finalRestriction ((proEtaleBaseChange (D.geometricFiber Y₀).hom).obj
    (ProEt.mk (𝟙 (Spec (.of D.k)))))).op x

/-- The specified sigma on final-object sections, in the sectionwise inverse-image model.
Source: blueprint point-transport formula, restriction--insertion--sheafification
(blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def sigma (n : ℕ)
    (M : integralOperationsFiniteModules l E (D.geometricFiber Y₀).left n)
    (x : (directSheaf D l E Y₀ n M).val.obj
      (op (ProEt.mk (𝟙 (Spec (.of D.k)))))) :=
  (directSheaf D l E Y₀ n M).val.map (frobeniusPointRestriction D).op x

/-- The specified p_g on Y sections, using its final object and the comma-normalized
sectionwise inverse-image model. This definition does not use B or the exchange.
Source: Stacks Tags 00VE, 00WX (blueprint: lem-pod-frobenius-exchange-degree-zero). -/
def sectionPullback (n : ℕ)
    (M : integralOperationsFiniteModules l E (D.geometricFiber Y₀).left n)
    (x : M.val.obj (op (ProEt.mk (𝟙 (D.geometricFiber Y₀).left)))) :=
  M.val.map (isoRestriction (FrobeniusExchange.galois D Y₀)).op x

/-- Degree-zero Frobenius exchange and transport equal the specified underived
inverse-image mate and section pullback. The first and last equations are written
with j=lambda⁻¹, so no inverse or identification is chosen as additional data.

Source: Stacks Tag 07A7, remark-base-change; blueprint
prop-cohomological-finiteness, Proof Step 7
(blueprint: lem-pod-frobenius-exchange-degree-zero).

Proof plan:
1. The Frobenius-square lemma gives the scheme automorphisms, their commuting
square, and its Cartesian identification (y,v) ↦ (g(y),v). Exact inverse image is
site relabelling, with scalar action transported through the constant comparison.
Thus j sends x to x tensor 1 and lambda sends x tensor b to c_A⁻¹(b)x.
2. Resolve M by a K-injective complex. A right adjoint to exact inverse image
preserves K-injectives. The pre-derived adjunction fraction formula identifies H⁰
of the specified derived unit-square-counit mate with its underived mate. Apply
right-derived-zero and exact-pullback homology comparisons to obtain clause one.
3. Exact sections on the geometric point commute with H⁰. The specified point
transport is Gamma(j) after restriction, insertion, and sheafification, giving
clause two with the canonical directZero identification.
4. The colimit adjunction counit evaluates on a generator by restriction along
squareArrow. On the final object its composite with restriction along h is exactly
restriction along g. This gives clause three, including the canonical projection
identifications of final-object sections.
5. Compose clauses one and two and use clause three. Since j=lambda⁻¹, the result
is clause four, equivalently Gamma(lambda) after H⁰(tau) equals p_g. All operations
are objectwise and include zero sheaves, empty Y, point Y, and disconnected Y. -/
theorem frobenius_exchange_degree_zero (n : ℕ)
    (M : integralOperationsFiniteModules l E (D.geometricFiber Y₀).left n)
    (_hM : @IsConstructibleProEtaleModuleSheaf _
      (Padic.coefficientExtensionRing l E (n + 1)) _
      (Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)) M)
    (_hRa : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n)
      (Spec (.of D.k))
      ((proEtaleConstantDerivedDirectImage (D.geometricFiber Y₀).hom
        (Padic.coefficientExtensionRing l E (n + 1))).obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) :
    (∀ (U : (Spec (.of D.k)).ProEt)
      (x : (directSheaf D l E Y₀ n M).val.obj
        (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U))),
      (frobeniusExchangeZero D l E Y₀ n M).val.app (op U)
        ((intrinsicUnit l E (frobeniusPointIso D).hom n
          (directSheaf D l E Y₀ n M)).val.app (op U) x) =
      (intrinsicUnit l E (FrobeniusExchange.galois D Y₀) n M).val.app
        (op ((proEtaleBaseChange (D.geometricFiber Y₀).hom).obj U))
        (frobeniusUnderivedMate D l E Y₀ n M U x)) ∧
    (∀ x : (directSheaf D l E Y₀ n M).val.obj
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))),
      iotaZero D l hl E Y₀ n M x =
        (intrinsicUnit l E (frobeniusPointIso D).hom n
          (directSheaf D l E Y₀ n M)).val.app
            (op (ProEt.mk (𝟙 (Spec (.of D.k))))) (sigma D l E Y₀ n M x)) ∧
    (∀ x : M.val.obj (op (ProEt.mk (𝟙 (D.geometricFiber Y₀).left))),
      frobeniusUnderivedMate D l E Y₀ n M (ProEt.mk (𝟙 (Spec (.of D.k))))
          (sigma D l E Y₀ n M (toPointSections D l E Y₀ n M x)) =
        M.val.map
          ((proEtaleIsoPostcompose (FrobeniusExchange.galois D Y₀)).map
            (finalRestriction ((proEtaleBaseChange (D.geometricFiber Y₀).hom).obj
              (ProEt.mk (𝟙 (Spec (.of D.k))))))).op
          (sectionPullback D l E Y₀ n M x)) ∧
    (∀ x : M.val.obj (op (ProEt.mk (𝟙 (D.geometricFiber Y₀).left))),
      transportZero D l hl E Y₀ n M (toPointSections D l E Y₀ n M x) =
        ((pull l E (FrobeniusExchange.galois D Y₀) n).obj M).val.map
          (finalRestriction ((proEtaleBaseChange (D.geometricFiber Y₀).hom).obj
            (ProEt.mk (𝟙 (Spec (.of D.k)))))).op
          ((intrinsicUnit l E (FrobeniusExchange.galois D Y₀) n M).val.app
            (op (ProEt.mk (𝟙 (D.geometricFiber Y₀).left)))
            (sectionPullback D l E Y₀ n M x))) := by
  sorry

end WeilConjectures.PodDegreeZero
