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

/-- The data left after the scalar packages and the two finite operations are chosen.
Source: Zheng, Construction 2.26 and Proposition 2.29; Stacks 0GL6 and 09AL
(blueprint: lem-sf-exceptional-finite-scalar-mates).

The proof is the ambient proper/open scalar-mate construction, transported through
the selected finite-Tor full subcategories.  In particular, it includes the
normalization equations and both adjoint shift equations required by `Construction`.
-/
structure ConstructionMaps
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f)
    (scalarX : Scalar l E L n m a X) (scalarY : Scalar l E L n m a Y)
    (source : Operation l E n c) (target : Operation l L m c) where
  q : source.F ⋙ scalarY.functor ≅ scalarX.functor ⋙ target.F
  b : source.G ⋙ scalarX.functor ≅ scalarY.functor ⋙ target.G
  q_normalized (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X) :
    ((finiteTorConstructible l L (m + 1) (Nat.succ_pos m) Y).ι).map (q.hom.app K) ≫
        target.left.hom.app ((scalarX.functor).obj K) =
      (pbcDerivedExtend (proEtaleConstantRingMap (T := Y) a)).map (source.left.hom.app K) ≫
        (leftScalarMap a c).app K.obj
  counit (N : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y) :
    q.hom.app (source.G.obj N) ≫ target.F.map (b.hom.app N) ≫
        target.adjunction.counit.app ((scalarY.functor).obj N) =
      (scalarY.functor).map (source.adjunction.counit.app N)
  qShift : q.hom.CommShift ℤ
  bShift : b.hom.CommShift ℤ
  etale : EtaleMates (RingHom.ulift.{u + 1, u + 1} a) c


end WeilConjectures.ExceptionalFiniteScalar
