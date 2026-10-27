/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import Sheaf.Paper.FiniteCompactSupportScalarTransport
public import Sheaf.Paper.EtaleCompactScalarCoherence
public import Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor
public import Sheaf.Paper.FiniteCtfTriangulated
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.RingedProjectionFirstShift
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit

/-! # Finite scalar mates for the constructible exceptional adjunction

Source: Zheng, Propositions 2.23, 2.29 and 3.16; Construction 2.26;
Stacks Project, Tags 0GL6, 09AL and 07A4
(blueprint: lem-sf-exceptional-finite-scalar-mates).

## Main definitions

* `Operation`, `Scalar`, `EtaleMates`, and `Construction` retain the actual
  functors, canonical realizations, adjunctions, scalar maps, and shift equations.

## Main statements

* `exceptionalFiniteScalarMates` asserts existence for every finite coefficient map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

/-- The existing triangulated closure supplies the inherited subcategory shifts.
Source: blueprint finite-Tor subcategory; Stacks 08G2
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
instance finiteTriangulated (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (T : Scheme.{u}) :
    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T).IsTriangulated :=
  (finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) T).2.1


/-- The chosen ordinary etale adjunction at the retained compactification.
Source: Zheng, Proposition 2.23; Stacks 0F5Y
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
def etaleAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  Adjunction.ofIsLeftAdjoint
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)

/-- Abbreviation for the right adjoint already selected by the ordinary adjunction.
Source: Zheng, Proposition 2.23
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
abbrev etaleExceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).rightAdjoint

/-- Canonical realization of the specified-compactification exceptional functor.
Source: blueprint exceptional inverse image; Stacks 09AL
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
def exceptional (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory X A :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    (ULift.{u + 1, u} A) c
  (sfIntrinsicDerivedEquivalence Y A).inverse ⋙
    ProEtale.sfFiniteExceptionalAt (ULift.{u + 1, u} A) c ⋙
    (sfIntrinsicDerivedEquivalence X A).functor

/-- The compact-support realization in inverse fixed-module coordinates.
Source: Stacks 09AL; the canonical proper/open site realization
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
def leftFixedIso (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) :
    (sfIntrinsicDerivedEquivalence Y A).inverse.obj ((sfIntrinsicCompactSupport c A).obj K) ≅
      (ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj
          ((sfIntrinsicDerivedEquivalence X A).inverse.obj K) :=
  (sfIntrinsicDerivedEquivalence Y A).inverse.mapIso
    ((sfIntrinsicCompactSupport c A).mapIso
      ((sfIntrinsicDerivedEquivalence X A).counitIso.app K).symm ≪≫
      (FiniteCompactScalar.compactRealizationIso A c).app
        ((sfIntrinsicDerivedEquivalence X A).inverse.obj K)) ≪≫
    ((sfIntrinsicDerivedEquivalence Y A).unitIso.app _).symm

/-- The actual ambient scalar-adjunction mate of the proper/open restriction square.
Source: Stacks 0GL6, 07A4; Zheng, Construction 2.26
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
def leftScalarMap {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (a : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    sfIntrinsicCompactSupport c A ⋙ pbcDerivedExtend (proEtaleConstantRingMap (T := Y) a) ⟶
      pbcDerivedExtend (proEtaleConstantRingMap (T := X) a) ⋙ sfIntrinsicCompactSupport c B :=
  ((mateEquiv (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := X) a))
    (pbcDerivedScalarAdjunction (proEtaleConstantRingMap (T := Y) a))).symm
      (TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c a).hom)).natTrans

/-- Literal full-subcategory restriction of the ambient scalar extension.
Source: Stacks 06YY and 09AL; finite scalar construction, step 2
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
def restrictScalar
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ) (T : Scheme.{u})
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    (h : ∀ K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) T,
      finiteTorConstructible l L (m + 1) (Nat.succ_pos m) T
        ((pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)).obj K.obj)) :
    finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) T ⥤
      finiteTorConstructibleCategory l L (m + 1) (Nat.succ_pos m) T :=
  (finiteTorConstructible l L (m + 1) (Nat.succ_pos m) T).lift
    ((finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T).ι ⋙
      pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)) h

/-- Expose the existing composite shift in the intrinsic compact-support coordinates.
Source: Stacks 03DI and 070K; exact open descent and K-injective proper image
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
instance compactShift (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sfIntrinsicCompactSupport c A).CommShift ℤ :=
  inferInstanceAs (((sfIntrinsicExtensionByZero c.i A).mapDerivedCategory ⋙
    proEtaleConstantDerivedDirectImage c.g A).CommShift ℤ)

/-- The finite operation with its actual realizations and transported adjunction.
The last field specifies the Hom bijection for every retained etale-origin witness.
Source: Zheng, Proposition 2.23; Stacks 09AL; finite construction, step 6
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
structure Operation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c : Compactification f) where
  F : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X ⥤
    finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y
  G : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y ⥤
    finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X
  left : F ⋙ (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Y).ι ≅
    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X).ι ⋙
      sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))
  right : G ⋙ (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X).ι ≅
    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Y).ι ⋙
      exceptional (Padic.coefficientExtensionRing l E (n + 1)) c
  adjunction : F ⊣ G
  [leftShift : F.CommShift ℤ]
  [rightShift : G.CommShift ℤ]
  unitShift : adjunction.unit.CommShift ℤ
  counitShift : adjunction.counit.CommShift ℤ
  leftShiftRealization : left.hom.CommShift ℤ
  normalized (hY : CompactSpace Y)
    (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X)
    (N : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y)
    (hK : DerivedCategory.TStructure.t.plus
      ((sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj
        K.obj))
    (hN : DerivedCategory.TStructure.t.plus
      ((sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj
        N.obj))
    (W : X.FixedEtaleOriginWitness (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n + 1))) ⟨_, hK⟩)
    (v : F.obj K ⟶ N) :
    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X).ι.map
        (adjunction.homEquiv K N v) ≫ right.hom.app N =
      ((sfIntrinsicDerivedEquivalence X
        (Padic.coefficientExtensionRing l E (n + 1))).counitIso.app K.obj).inv ≫
        (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1))).functor.map
          (@ProEtale.specifiedExceptionalHomEquiv _ _ _ _ _ _ _ hY c
            (Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) c)
            ⟨_, hK⟩ W ⟨_, hN⟩
            ((leftFixedIso (Padic.coefficientExtensionRing l E (n + 1)) c K.obj).inv ≫
              (sfIntrinsicDerivedEquivalence Y
                (Padic.coefficientExtensionRing l E (n + 1))).inverse.map
                  (left.inv.app K ≫
                    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Y).ι.map v)))

attribute [instance] Operation.leftShift Operation.rightShift

/-- The canonical restriction comparison for exceptional right adjoints: the
right-adjoint uniqueness isomorphism of the scalar/exceptional Hom chain.
Source: Zheng, Proposition 2.23; Stacks 0GL6; finite scalar proof, step 4
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
def restrictionIso {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (a : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (q : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        Etale.scalarExtension a Y ≅ Etale.scalarExtension a X ⋙
          Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c) :
    (etaleExceptional B c) ⋙ Sheaf.derivedRestrictScalars X.smallEtaleTopology a ≅
      Sheaf.derivedRestrictScalars Y.smallEtaleTopology a ⋙ (etaleExceptional A c) :=
  ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology a)).comp
        (etaleAdjunction B c)).rightAdjointUniq
    (((etaleAdjunction A c).comp (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a))).ofNatIsoLeft q)

/-- The scalar shift adjoint to the exact termwise restriction shift.
Source: Stacks 06YY; adjoint shift normalization
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
instance etaleScalarShift {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) (T : Scheme.{u}) : (Etale.scalarExtension a T).CommShift ℤ :=
  (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology a)).leftAdjointCommShift ℤ

/-- Ambient etale realizations of the two scalar mates and the constant-B tensor
calculation. The projection is the existing ordered projection followed by the
canonical pullback of the constant coefficient complex. Its inverse therefore gives
exactly the constant-coefficient exceptional tensor transpose, even for nonflat B.
Source: Zheng, Construction 2.26 and Proposition 2.29(2); Stacks 0GL6
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
structure EtaleMates {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (a : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) where
  q : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
      Etale.scalarExtension a Y ≅ Etale.scalarExtension a X ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
  q_normalized : q.hom = Etale.compactScalarMap a c
  properShift : (Etale.scalarMate a c.g).CommShift ℤ
  openShift : (Etale.ExceptionalCoefficients.openIso a c.i).hom.CommShift ℤ
  b : (etaleExceptional A c) ⋙ Etale.scalarExtension a X ≅
    Etale.scalarExtension a Y ⋙ (etaleExceptional B c)
  b_normalized : b.hom =
    (mateEquiv (etaleAdjunction A c) (etaleAdjunction B c)
      (TwoSquare.mk _ _ _ _ q.inv)).natTrans
  projection :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        Etale.scalarExtension a Y ⋙ Sheaf.derivedRestrictScalars Y.smallEtaleTopology a ≅
      (Etale.scalarExtension a X ⋙ Sheaf.derivedRestrictScalars X.smallEtaleTopology a) ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  projection_normalized (K : Etale.DerivedCategoryModule A X) :
    projection.hom.app K =
      (Etale.scalarTensorIso a Y).hom.app
          ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K) ≫
        ((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K).app
          (Etale.scalarCoefficient a Y) ≫
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj K).map
              (Etale.scalarCoefficientPullbackIso a f).hom ≫
            (Etale.scalarTensorIso a X).inv.app K)
  projectionShift : projection.hom.CommShift ℤ
  restricted_b (N : Etale.DerivedCategoryModule A Y) :
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology a).map (b.hom.app N) ≫
        (restrictionIso a c q).hom.app ((Etale.scalarExtension a Y).obj N) =
      (etaleAdjunction A c).homEquiv _ _
        (projection.inv.app ((etaleExceptional A c).obj N) ≫
          (Etale.scalarExtension a Y ⋙ Sheaf.derivedRestrictScalars
            Y.smallEtaleTopology a).map ((etaleAdjunction A c).counit.app N))

/-- Scalar preservation, its unchanged Tor interval, and the literal restricted
functor with the equality realization. Shift compatibility is imposed on that
realization, so the restricted shift is inherited from the ambient derived tensor.
Source: Stacks 06YY, 09AL and 07A4; finite scalar construction, steps 1--2
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
structure Scalar
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1)) (T : Scheme.{u}) where
  preserves (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) T) :
    finiteTorConstructible l L (m + 1) (Nat.succ_pos m) T
      ((pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)).obj K.obj)
  torInterval (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) T) (r s : ℤ) :
    HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (n + 1)) K.obj r s →
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l L (m + 1))
        ((pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)).obj K.obj) r s
  scalar_eq : restrictScalar l E L n m T a preserves ⋙
      (finiteTorConstructible l L (m + 1) (Nat.succ_pos m) T).ι =
    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T).ι ⋙
      pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)
  [commShift : (restrictScalar l E L n m T a preserves).CommShift ℤ]
  realizationShift : (eqToIso scalar_eq).hom.CommShift ℤ

/-- The literal restricted functor, with its scalar package visible for instance search.
Source: Stacks 06YY, 09AL (blueprint: lem-sf-exceptional-finite-scalar-mates). -/
def Scalar.functor
    {l : ℕ} [Fact l.Prime]
    {E L : Type u} [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    {n m : ℕ}
    {a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1)} {T : Scheme.{u}}
    (S : Scalar l E L n m a T) :=
  restrictScalar l E L n m T a S.preserves

/-- The shift structure retained by the scalar package.
Source: Stacks 06YY, 09AL (blueprint: lem-sf-exceptional-finite-scalar-mates). -/
instance Scalar.functorShift
    {l : ℕ} [Fact l.Prime]
    {E L : Type u} [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    {n m : ℕ}
    {a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1)} {T : Scheme.{u}}
    (S : Scalar l E L n m a T) : S.functor.CommShift ℤ := S.commShift

/-- All finite scalar conclusions on the actual full subcategories. Every ring map is
retained, rather than only an inductively generated list of coefficient changes.
Source: Zheng, Propositions 2.23 and 2.29; Stacks 09AL, 0GL6 and 07A4
(blueprint: lem-sf-exceptional-finite-scalar-mates). -/
structure Construction
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f) where
  scalarX : Scalar l E L n m a X
  scalarY : Scalar l E L n m a Y
  source : Operation l E n c
  target : Operation l L m c
  q : source.F ⋙ scalarY.functor ≅
    scalarX.functor ⋙ target.F
  b : source.G ⋙ scalarX.functor ≅
    scalarY.functor ⋙ target.G
  q_normalized (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X) :
    (finiteTorConstructible l L (m + 1) (Nat.succ_pos m) Y).ι.map (q.hom.app K) ≫
        target.left.hom.app ((scalarX.functor).obj K) =
      (pbcDerivedExtend (proEtaleConstantRingMap (T := Y) a)).map (source.left.hom.app K) ≫
        (leftScalarMap a c).app K.obj
  counit (N : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y) :
    q.hom.app (source.G.obj N) ≫ target.F.map (b.hom.app N) ≫
        target.adjunction.counit.app
          ((scalarY.functor).obj N) =
      (scalarY.functor).map (source.adjunction.counit.app N)
  qShift : q.hom.CommShift ℤ
  bShift : b.hom.CommShift ℤ
  etale : EtaleMates (RingHom.ulift.{u + 1, u + 1} a) c

/-- Finite scalar extension preserves the actual constructible finite-Tor categories
and their Tor intervals, with literal restrictions and the canonical scalar mates.
Quotient, ramified, identity and composite unital maps are all quantified directly.

Source: Zheng, Propositions 2.23, 2.29 and 3.16, Construction 2.26; Stacks 0GL6,
09AL, 09B1 and 07A4 (blueprint: lem-sf-exceptional-finite-scalar-mates).

Proof plan (the eight steps of the DAG node):

1. First work on the ordinary etale categories. For $K\in\mathcal C_{T,A}$, constructible origin
and Tor comparison give an etale object $K^e$ with the same Tor interval $[u,v]$. The
constructible variant of the flat-model lemma applies because $T$ is finite type over $k$: choose
a flat constructible model $P$ supported in $[u,v]$. A bounded complex of flat sheaves is K-flat,
so derived change of rings computes $K^e\otimes_A^LB$ by $P\otimes_AB$, canonically on morphisms
and independently of this model. Each term is flat over $B$: for an injection $M\hookrightarrow N$
of $B$-module sheaves, $(P^i\otimes_AB)\otimes_BM=P^i\otimes_A\operatorname{Res}M$, and flatness
of $P^i$ preserves this injection. On any stratum trivializing $P^i$, its tensor with the finite
ring $B$ is finite locally constant. Take a common finite refinement for the finitely many terms.
The constructible Serre theorem gives constructible kernels, images and cohomology. The same flat
complex supported in $[u,v]$ therefore has Tor interval $[u,v]$ over $B$, including for nonflat
$A\to B$. Uses: lem-sf-proetale-constructible-origin, lem-sf-comparison-tor-amplitude,
lem-sf-flat-model, lem-pur-derived-change-of-rings, thm-constructible-serre,
lem-weil-pbc-independent-bounded-flat-kflat.

2. Exact comparison inverse image and the canonical derived pullback/tensor identification
identify $\nu_T^*(P\otimes_AB)$ with $S_{a,T}(\nu_T^*P)$. The constructible-origin and
Tor-comparison theorems carry the conclusion of step 1 back to the actual pro-etale category, with
the unchanged interval. Define $T_{a,T}$ on objects by the ambient $S_{a,T}$ with this membership
proof and on morphisms by $S_{a,T}$ itself. The subcategory is full, so identities and composition
are literally those of the ambient functor: $I_{T,B}T_{a,T}=S_{a,T}I_{T,A}$, with equality
realization. Exactness and its canonical shifts are inherited from derived change of rings. This
construction applies separately to every actual finite ring map, including an identity or a
composite. Uses: lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-sf-proetale-constructible-origin, lem-sf-comparison-tor-amplitude,
lem-pur-derived-change-of-rings.

3. Write $F^e_R=Rp_{c,\mathrm{et},R,*}j^e_{!,R}$ and $G^e_R=f^\times_{c,R}$ on the entire etale
derived categories. Use their ambient adjunctions, with counits $\epsilon^e_R$. Let $q^e_a$ be
exactly the proper coefficient comparison at $j^e_{!,A}(-)$ followed by $Rp_{c,B,*}$ of the open
scalar tensor map. The proper comparison theorem specifies its transpose as scalar extension of
the proper counit after the canonical pullback/tensor identification; the open map is scalar
balancing on the open and zero off it. The compact scalar coherence theorem proves this specified
composite invertible for any finite $A\to B$, with no flatness assumption. Thus
$q^e_a:S_YF^e_A\cong F^e_BS_X$ is the required left map rather than an independently chosen
isomorphism. Uses: thm-amb-etale-exceptional-adjoint, lem-asd-proper-finite-coefficient-extension,
lem-pur-etale-compact-scalar-coherence.

4. Put $U_T=\operatorname{Res}_{a,T}$. Derived ringed direct-image composition applied to the two
factorizations of the same ringed-topos map gives $U_YRp_{c,B,*}\cong Rp_{c,A,*}U_{\overline X}$.
Open extension by zero commutes with $U$ termwise: it changes only the ring action on the open and
both sides are zero off the open. Consequently $h:U_YF^e_B\cong F^e_AU_X$ is the canonical
restriction comparison. For any $N\in D(Y_{\mathrm{et}},B)$ and $K\in D(X_{\mathrm{et}},A)$ the
scalar adjunction, the two exceptional adjunctions and $q^e_a$ give natural bijections
$$\operatorname{Hom}_A(K,U_XG^e_BN)\cong\operatorname{Hom}_B(S_XK,G^e_BN)\cong\operatorname{Hom}_B
(F^e_BS_XK,N)\cong\operatorname{Hom}_B(S_YF^e_AK,N)\cong\operatorname{Hom}_A(K,G^e_AU_YN).$$
Yoneda gives a canonical isomorphism $d_N:U_XG^e_BN\cong G^e_AU_YN$. Explicitly $d_N$ is the
transpose of
$F^e_AU_XG^e_BN\xrightarrow{h^{-1}}U_YF^e_BG^e_BN\xrightarrow{U_Y\epsilon^e_{B,N}}U_YN$. Indeed,
following $\mathrm{id}$ through the chain, its image is
$U_Y(\epsilon^e_{B,N}F^e_B(c)\,q^e)\circ\eta$, with $\eta:x\mapsto x\otimes1$ the scalar unit and
$c:x\otimes b\mapsto b\,x$ the scalar counit. By the proper coefficient theorem and the open
balancing map, $h\circ U_Yq^e_K$ is the projection map $P_K:B_Y\otimes^L_AF^e_AK\to
F^e_A(B_X\otimes^L_AK)$. Naturality of $h$ then rewrites the image as
$U_Y\epsilon^e_{B,N}\,h^{-1}\,F^e_A(U_Xc)\,P\,\eta$. Since $P$ is natural in the constant factor
and is the identity for the unit $A$, $F^e_A(U_Xc)\,P\,\eta=\mathrm{id}$. Uses:
lem-weil-pbc-ringed-topoi-derived-pushforward-composition,
lem-pur-sheaf-ring-derived-coefficient-adjunction, thm-amb-etale-exceptional-adjoint,
lem-galois-yoneda-hom-bijection, lem-pur-etale-compact-scalar-coherence,
lem-asd-proper-finite-coefficient-extension, lem-weil-pbc-ringed-projection-mate-exact.

5. For $L\in D(Y_{\mathrm{et}},A)$ define $b^e_{a,L}$ to be the $F^e_B\dashv G^e_B$ transpose of
$$F^e_BS_XG^e_AL\xrightarrow{(q^e_{a,G^e_AL})^{-1}}S_YF^e_AG^e_AL\xrightarrow{S_Y\epsilon^e_{A,L}}
S_YL.$$
The adjunction bijection gives naturality in $L$ and exactly
$$\epsilon^e_{B,S_YL}\,F^e_B(b^e_{a,L})\,q^e_{a,G^e_AL}=S_Y\epsilon^e_{A,L}.$$ Under $d_{S_YL}$
and $U_TS_T(-)=B_T\otimes_A^L(-)$, its restriction has $F^e_A$-transpose
$$F^e_A(B_X\otimes_A^LG^e_AL)\xrightarrow{P^{-1}}B_Y\otimes_A^LF^e_AG^e_AL\xrightarrow{1\otimes\ep
silon^e_{A,L}}B_Y\otimes_A^LL.$$
Indeed substitute the transpose formula for $d$ from step 4 into the preceding counit equation;
$U_Yq^e$ is $P$, since its proper factor is precisely the ordered projection by the proper
coefficient theorem and its open factor is the balancing map. Naturality of $h$ and the counit
equation replace $U_Y\epsilon^e_B\,U_YF^e_B(b^e)$ by $U_YS_Y\epsilon^e_A\,(U_Yq^e)^{-1}$. This is
the displayed formula. It is the defining transpose of the exceptional constant-$B$ tensor map.
The constant-tensor theorem applies to $B\in D(A\text{-}\mathrm{Mod})$ without requiring
perfection or bounded projective dimension, so this restricted map is invertible. Restriction
detects quasi-isomorphisms: the cohomology of a cone is unchanged as an abelian sheaf. Hence the
$B$-linear map $b^e_a$ is invertible. Uses: thm-amb-etale-exceptional-adjoint,
lem-pur-sheaf-ring-derived-coefficient-adjunction, lem-asd-proper-finite-coefficient-extension,
lem-pur-etale-compact-scalar-coherence, lem-pur-etale-exceptional-constant-tensor.

6. The finite-operations theorem supplies the actual constructible restrictions of $F_R,G_R$,
their adjunction and their adjoint shift structures, without absolute separatedness. Steps 1–2
apply both to its inputs and to $F_RK,G_RL$, so every endpoint of $q,b$ lies in the stated full
categories. Use constructible origin and the invertible bounded-below site-comparison unit to
transport $q^e,b^e$ through $\nu^*$ and $R\nu_*$. The compact-support comparison identifies
$\nu_Y^*F^e_R$ with $F_R\nu_X^*$; the exceptional realization is $G_R=\nu_X^*G^e_RR\nu_{Y,*}$. Its
unit and counit are precisely those of the transported adjunction. Applying the equivalence to the
equation in step 5 therefore gives
$$\epsilon_{B,T_{a,Y}L}F_B(b_{a,L})q_{a,G_AL}=T_{a,Y}(\epsilon_{A,L}).$$ Fullness identifies the
transported arrows with natural transformations on the actual full subcategories, and full
faithfulness makes this the unique transpose there. Uses: lem-sf-exceptional-finite-operations,
lem-sf-proetale-constructible-origin, thm-weil-pbc-site-comparison,
lem-sf-class-compact-support-comparison.

7. For the realization of $q$, expand the compact-support site comparison into its two factors.
The proper factor is the counit-normalized direct-image mate, not an unspecified site isomorphism.
The open factor is the termwise comparison $\nu_{\overline X}^*j^e_!\cong j^p_!\nu_X^*$.
Substitute their defining counit and open-unit transposes into step 3. The adjacent site units
cancel with the site counits, and the remaining proper transpose is the scalar extension of the
same proper counit followed by the same open balancing map. The tensor/pullback comparison
identifies the intervening tensors on K-flat models. Thus this transport is exactly the pro-etale
proper scalar-adjunction mate followed by the open tensor map. The counit equation of step 6 then
identifies $b$ with its required normalized transpose; no second choice of Hom bijections is
introduced. The restriction description in step 5 transports to etale-origin objects using these
same identifications and site units. Uses: lem-weil-pbc-comparison-direct-image-canonical-mate,
lem-cbc-proetale-extension-zero-comparison, lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-asd-proper-finite-coefficient-extension, lem-pur-sheaf-ring-derived-coefficient-adjunction.

8. All shift equations use the chosen derived shifts. Derived change of rings is exact. The
pullback/tensor comparison commutes with integer shifts; the proper projection map commutes with
shifts in the direct-image input by the first-variable projection theorem (and in the tensor input
by the ringed projection theorem). For the proper scalar map, transpose its proposed shift
equation: its counit formula and the pullback/tensor shift equation give identical transposes,
hence equal maps. This uses the scalar map itself and does not infer equality from restriction of
scalars. The open map is induced by the degreewise balancing identity. On the total tensor
complexes both paths shift the same summand and have the same tensor sign, so it commutes with
shifts in either input. The site comparison is termwise on inverse images and its direct-image
comparison is the mate using the adjoint shifts. Composition and whiskering preserve shift
equations. Consequently $q$ has the required shift equation. Transpose the two sides of the
proposed shift equation for $b$: by shift compatibility of the fixed counits, each transpose is
$T_Y\epsilon_A\,(q_{G_A})^{-1}$ with the same shift identifications. Injectivity of the adjunction
bijection makes the two arrows equal. This also proves compatibility for every integer, with the
unique adjoint shift structure. Uses: lem-pur-derived-change-of-rings,
lem-weil-pbc-ringed-projection-mate-exact, lem-sfb-ringed-projection-first-shift,
lem-pur-etale-open-derived-tensor, lem-weil-pbc-adjunction-shift-compatibility-unique,
lem-weil-pbc-commshift-nattrans-comp-whisker, thm-amb-etale-exceptional-adjoint.
-/
theorem exceptionalFiniteScalarMates
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : Nonempty (Construction l E L n m a c) := by
  sorry

end WeilConjectures.ExceptionalFiniteScalar
