/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.AdicExceptionalProjectionData
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.ExceptionalCoefficientComparison
public import Sheaf.SixFunctors.FiniteDualizing

/-! # Coefficient coherence for the adic adjunctions
Source: Bhatt--Scholze Remark 6.8.15
(blueprint: def-per-adic-exceptional-scalar-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicExceptionalProjection

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]

/-- The already constructed integral scalar extension, restricted to the actual category.
Source: Remark 6.8.15 (blueprint: def-per-adic-exceptional-scalar-data). -/
abbrev scalar (E L : Coefficient.{u} l) (i : E.carrier →ₐ[ℚ_[l]] L.carrier)
    (X : Spaces k) : C l E X ⥤ C l L X :=
  integralComparisonConstructibleScalar l E.carrier L.carrier i X.scheme

/-- Finite scalar extension in the fixed realization, transported by the specified
intrinsic equivalences. Source: Remark 6.8.15
(blueprint: def-per-adic-exceptional-scalar-data). -/
def finiteScalar {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Spaces k) :=
  (sfIntrinsicDerivedEquivalence X.scheme A).inverse ⋙
    ProEtale.pbcFixedScalarExtension (ProEt.topology X.scheme) φ.ulift.{u + 1, u + 1} ⋙
      (sfIntrinsicDerivedEquivalence X.scheme B).functor

/-- The scalar map on intrinsic constant rings, retaining the actual quotient action.
Source: Stacks 03CO (blueprint: def-per-adic-exceptional-scalar-data). -/
def finiteScalarRingMap {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Spaces k) :=
  (constantSheaf (ProEt.topology X.scheme) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (R := ULift.{u + 1} A) (S := ULift.{u + 1} B)
      φ.ulift.{u + 1, u + 1})

/-- Scalar realization is the conjugate of the existing section-normalized restriction
comparison. No new extension or unspecified isomorphism is selected.
Source: Stacks 03CO, 06YY (blueprint: def-per-adic-exceptional-scalar-data). -/
def finiteScalarInverseRealization {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (X : Spaces k) :
    pbcDerivedExtend (finiteScalarRingMap φ X) ⋙
        (sfIntrinsicDerivedEquivalence X.scheme B).inverse ≅
      (sfIntrinsicDerivedEquivalence X.scheme A).inverse ⋙
        ProEtale.pbcFixedScalarExtension (ProEt.topology X.scheme) φ.ulift.{u + 1, u + 1} :=
  ((conjugateIsoEquiv
    ((pbcDerivedScalarAdjunction (finiteScalarRingMap φ X)).comp
      (sfIntrinsicDerivedEquivalence X.scheme B).symm.toAdjunction)
    ((sfIntrinsicDerivedEquivalence X.scheme A).symm.toAdjunction.comp
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (ProEt.topology X.scheme) φ.ulift.{u + 1, u + 1})))).symm
      (finiteDualizingGenericDerivedRestriction X.scheme φ)).symm

/-- The actual derived tensor along the finite quotient map has this fixed realization.
Source: Stacks 06YY (blueprint: def-per-adic-exceptional-scalar-data). -/
def finiteScalarBridge {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Spaces k) :
    pbcDerivedExtend (finiteScalarRingMap φ X) ≅ finiteScalar φ X :=
  Functor.isoWhiskerLeft _ (sfIntrinsicDerivedEquivalence X.scheme B).counitIso.symm ≪≫
    Functor.isoWhiskerRight (finiteScalarInverseRealization φ X)
      (sfIntrinsicDerivedEquivalence X.scheme B).functor

/-- The comparison-direct-image scalar arrow is the transpose of the comparison
inverse-image scalar isomorphism followed by the actual comparison counit.
Source: Stacks 07A6, 099R (blueprint: def-per-adic-exceptional-scalar-data). -/
def finiteComparisonScalar {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Spaces k)
    (M : DerivedCategory (Sheaf (ProEt.topology X.scheme) (ModuleCat.{u + 1} A))) :
    (Etale.scalarExtension φ X.scheme).obj
        ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A)
          X.scheme).rightDerivedFunctor.obj M) ⟶
      (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} B) X.scheme).rightDerivedFunctor.obj
        ((ProEtale.pbcFixedScalarExtension (ProEt.topology X.scheme) φ).obj M) :=
  (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} B) X.scheme).homEquiv _ _
    ((ProEtale.pbcComparisonReduction X.scheme φ).inv.app _ ≫
      (ProEtale.pbcFixedScalarExtension (ProEt.topology X.scheme) φ).map
        ((ProEtale.derivedComparisonAdjunction
          (ModuleCat.{u + 1} A) X.scheme).counit.app M))

/-- The finite exceptional coefficient map is the specified etale compact-support
mate, transported through the actual comparison-site scalar arrows.
Source: Bhatt--Scholze 6.7.18, 6.8.15
(blueprint: def-per-adic-exceptional-scalar-data). -/
def finiteExceptionalFixedScalar {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f))
    (M : DerivedCategory (Sheaf (ProEt.topology Y.scheme)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    (ProEtale.pbcFixedScalarExtension (ProEt.topology X.scheme)
      φ.ulift.{u + 1, u + 1}).obj ((ProEtale.sfFiniteExceptionalFixed A c).obj M) ⟶
      (ProEtale.sfFiniteExceptionalFixed B c).obj
        ((ProEtale.pbcFixedScalarExtension (ProEt.topology Y.scheme)
          φ.ulift.{u + 1, u + 1}).obj M) := by
  letI := c.hasCompactification
  exact (ProEtale.pbcComparisonReduction X.scheme φ.ulift.{u + 1, u + 1}).hom.app _ ≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
      X.scheme).mapDerivedCategory.map
      (Etale.ExceptionalCoefficients.mateMap φ.ulift.{u + 1, u + 1} (arrow f) _ ≫
        (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (ULift.{u + 1} B)) (arrow f)).map
          (finiteComparisonScalar φ.ulift.{u + 1, u + 1} Y M))

/-- Intrinsic finite exceptional scalar comparison, defined by the finite
compact-support mate, not by the integral exceptional comparison.
Source: Bhatt--Scholze 6.8.15 (blueprint: def-per-adic-exceptional-scalar-data). -/
def finiteExceptionalScalar {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f)) (M : proEtaleDerivedCategory Y.scheme A) :
    (finiteScalar φ X).obj ((ProEtale.sfFiniteExceptional A c).obj M) ⟶
      (ProEtale.sfFiniteExceptional B c).obj ((finiteScalar φ Y).obj M) :=
  (sfIntrinsicDerivedEquivalence X.scheme B).functor.map
    ((ProEtale.pbcFixedScalarExtension (ProEt.topology X.scheme)
        φ.ulift.{u + 1, u + 1}).map
      ((sfIntrinsicDerivedEquivalence X.scheme A).unitIso.inv.app _) ≫
      finiteExceptionalFixedScalar φ f c
        ((sfIntrinsicDerivedEquivalence Y.scheme A).inverse.obj M) ≫
      (ProEtale.sfFiniteExceptionalFixed B c).map
        ((sfIntrinsicDerivedEquivalence Y.scheme B).unitIso.hom.app _))

/-- Retained quotient map with its forced target-index transport. Natural index m
means exponent m+1, so hm retains exactly the target exponent e*(n+1).
Source: Bhatt--Scholze 6.8.15 (blueprint: def-per-adic-exceptional-scalar-data). -/
def ramifiedFiniteMap (E L : Coefficient.{u} l) (i : E.carrier →ₐ[ℚ_[l]] L.carrier)
    (e : ℕ) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
    (n m : ℕ) (hm : m + 1 = e * (n + 1)) :
    Padic.coefficientExtensionRing l E.carrier (n + 1) →+*
      Padic.coefficientExtensionRing l L.carrier (m + 1) :=
  (RingEquiv.cast (R := Padic.coefficientExtensionRing l L.carrier) hm.symm).toRingHom.comp
    (PurCompactSupport.ramifiedMap l E.carrier L.carrier i e he (n + 1))

/-- Natural scalar identity, composition, tensor, and ordinary-completion comparisons.
Their components are fixed by the published representative-normalized maps.
Source: Remark 6.8.15 (blueprint: def-per-adic-exceptional-scalar-data). -/
structure Scalars where
  unit : ∀ (E : Coefficient.{u} l) (X : Spaces k),
    scalar l E E (AlgHom.id ℚ_[l] E.carrier) X ≅ 𝟭 (C l E X)
  unitNormalization : ∀ (E : Coefficient.{u} l) (X : Spaces k) (K : C l E X),
    ((unit E X).hom.app K).hom =
      (integralComparisonScalarUnit l E.carrier X.scheme K).hom
  comp : ∀ (E L N : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) (j : L.carrier →ₐ[ℚ_[l]] N.carrier)
    (X : Spaces k), scalar l E L i X ⋙ scalar l L N j X ≅ scalar l E N (j.comp i) X
  compNormalization : ∀ (E L N : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) (j : L.carrier →ₐ[ℚ_[l]] N.carrier)
    (X : Spaces k) (K : C l E X), ((comp E L N i j X).hom.app K).hom =
      (integralComparisonScalarAssociator l E.carrier L.carrier i N.carrier j X.scheme K).hom
  tensor : ∀ (E L : Coefficient.{u} l) (i : E.carrier →ₐ[ℚ_[l]] L.carrier) (X : Spaces k),
    AdicExceptionalProjection.tensor l E X ⋙ scalar l E L i X ≅
      (scalar l E L i X).prod (scalar l E L i X) ⋙ AdicExceptionalProjection.tensor l L X
  tensorNormalization : ∀ (E L : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) (X : Spaces k) (K M : C l E X),
    ((tensor E L i X).hom.app (K, M)).hom =
      (scalarTensorCompleted l E.carrier L.carrier i X.scheme K.obj M.obj
        K.property.1 M.property.1
        ((AdicExceptionalProjection.tensor l E X).obj (K, M)).property.1).hom
  realization : ∀ (E L : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) (X : Spaces k),
    (sfIntegralConstructible l E.carrier X.scheme).ι ⋙
      pbcDerivedExtend (completedCoefficientMap l E.carrier L.carrier i
        X.scheme) ≅ scalar l E L i X ⋙ (sfIntegralConstructible l L.carrier X.scheme).ι
  realizationNormalization : ∀ (E L : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) (X : Spaces k) (K : C l E X),
    (realization E L i X).hom.app K =
      (completedScalarComparison l E.carrier L.carrier i X.scheme).app K.obj
  ramifiedSquare : ∀ (E L : Coefficient.{u} l) (i : E.carrier →ₐ[ℚ_[l]] L.carrier)
    (e : ℕ) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e) (_hepos : 1 ≤ e)
    (n m : ℕ) (hm : m + 1 = e * (n + 1)) (X : Spaces k),
    completedCoefficientMap l E.carrier L.carrier i X.scheme ≫
        PurCompactSupport.projection l L.carrier (m + 1) (Nat.succ_pos m) X.scheme =
      PurCompactSupport.projection l E.carrier (n + 1) (Nat.succ_pos n) X.scheme ≫
        finiteScalarRingMap (ramifiedFiniteMap l E L i e he n m hm) X

/-- Scalar shift is ordinary derived tensor's normalized shift, transported by the
fixed completion comparison and the fully faithful constructible inclusion.
Source: Remark 6.8.15 (blueprint: def-per-adic-exceptional-scalar-data). -/
@[instance_reducible]
def Scalars.shift (S : Scalars (k := k) l) (E L : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) (X : Spaces k) :
    (scalar l E L i X).CommShift ℤ :=
  Functor.CommShift.ofComp (S.realization E L i X).symm ℤ

/-- Canonical balancing of scalar extension and a finite reduction. The given square
is a square of the actual completed inclusion and the two quotient projections.
Source: Remark 6.8.15 (blueprint: def-per-adic-exceptional-scalar-data). -/
def Scalars.finiteBalance (S : Scalars (k := k) l) (E L : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) (n m : ℕ)
    (φ : Padic.coefficientExtensionRing l E.carrier (n + 1) →+*
      Padic.coefficientExtensionRing l L.carrier (m + 1))
    (h : ∀ X : Spaces k,
      completedCoefficientMap l E.carrier L.carrier i X.scheme ≫
          PurCompactSupport.projection l L.carrier (m + 1) (Nat.succ_pos m) X.scheme =
        PurCompactSupport.projection l E.carrier (n + 1) (Nat.succ_pos n) X.scheme ≫
          finiteScalarRingMap φ X)
    (X : Spaces k) (K : C l E X) :
    (red l L X m).obj ((scalar l E L i X).obj K) ≅
      (finiteScalar φ X).obj ((red l E X n).obj K) :=
  (scalarReductionDerivedExtension l L.carrier X.scheme m).mapIso
      ((S.realization E L i X).symm.app K) ≪≫
    (PurCompactSupport.finiteReductionIso l L.carrier X.scheme m).symm.app _ ≪≫
    (PurCompactSupport.tensorSquare
      (completedCoefficientMap l E.carrier L.carrier i X.scheme) (finiteScalarRingMap φ X)
      (PurCompactSupport.projection l E.carrier (n + 1) (Nat.succ_pos n) X.scheme)
      (PurCompactSupport.projection l L.carrier (m + 1) (Nat.succ_pos m) X.scheme)
      (h X)).app K.obj ≪≫
    (pbcDerivedExtend (finiteScalarRingMap φ X)).mapIso
      ((PurCompactSupport.finiteReductionIso l E.carrier X.scheme n).app K.obj) ≪≫
    (finiteScalarBridge φ X).app ((red l E X n).obj K)

/-- A scalar comparison for a family of functors, with literal identity and tower equations.
Source: Remark 6.8.15 (blueprint: def-per-adic-exceptional-scalar-data). -/
structure ScalarFunctor (S : Scalars (k := k) l) (X Y : Spaces k)
    (A : ∀ E : Coefficient.{u} l, C l E X ⥤ C l E Y) where
  iso : ∀ (E L : Coefficient.{u} l) (i : E.carrier →ₐ[ℚ_[l]] L.carrier),
    A E ⋙ scalar l E L i Y ≅ scalar l E L i X ⋙ A L
  identity : ∀ (E : Coefficient.{u} l) (K : C l E X),
    (iso E E (AlgHom.id ℚ_[l] E.carrier)).hom.app K ≫ (A E).map ((S.unit E X).hom.app K) =
      (S.unit E Y).hom.app ((A E).obj K)
  tower : ∀ (E L N : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) (j : L.carrier →ₐ[ℚ_[l]] N.carrier) (K : C l E X),
    (scalar l L N j Y).map ((iso E L i).hom.app K) ≫
      (iso L N j).hom.app ((scalar l E L i X).obj K) ≫
      (A N).map ((S.comp E L N i j X).hom.app K) =
        (S.comp E L N i j Y).hom.app ((A E).obj K) ≫ (iso E N (j.comp i)).hom.app K

/-- The unit and counit squares expressing that the right-hand scalar comparison is the
adjoint mate of the left-hand one. Source: Remark 6.8.15
(blueprint: def-per-adic-exceptional-scalar-data). -/
structure ScalarAdjunction (S : Scalars (k := k) l) (X Y : Spaces k)
    (F : ∀ E : Coefficient.{u} l, C l E X ⥤ C l E Y)
    (G : ∀ E : Coefficient.{u} l, C l E Y ⥤ C l E X)
    (a : ∀ E : Coefficient.{u} l, ExactAdjunction l E X Y (F E) (G E))
    (q : ScalarFunctor l S X Y F) (b : ScalarFunctor l S Y X G) where
  unit : ∀ (E L : Coefficient.{u} l) (i : E.carrier →ₐ[ℚ_[l]] L.carrier) (K : C l E X),
    (scalar l E L i X).map ((a E).adj.unit.app K) ≫
      (b.iso E L i).hom.app ((F E).obj K) ≫
      (G L).map ((q.iso E L i).hom.app K) =
        (a L).adj.unit.app ((scalar l E L i X).obj K)
  counit : ∀ (E L : Coefficient.{u} l) (i : E.carrier →ₐ[ℚ_[l]] L.carrier) (M : C l E Y),
    (q.iso E L i).hom.app ((G E).obj M) ≫
      (F L).map ((b.iso E L i).hom.app M) ≫
      (a L).adj.counit.app ((scalar l E L i Y).obj M) =
        (scalar l E L i Y).map ((a E).adj.counit.app M)

/-- All four coefficient comparisons at one arrow, with their specified normalizations.
Source: Remark 6.8.15 (blueprint: def-per-adic-exceptional-scalar-data). -/
structure ScalarOperation (S : Scalars (k := k) l) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f)) (O : ∀ E : Coefficient.{u} l, Operation l E f c) where
  pull : ScalarFunctor l S Y X (fun E ↦ AdicExceptionalProjection.pull l E f)
  direct : ScalarFunctor l S X Y (fun E ↦ (O E).direct)
  support : ScalarFunctor l S X Y (fun E ↦ AdicExceptionalProjection.support l E f c)
  exceptional : ScalarFunctor l S Y X (fun E ↦ (O E).exceptional)
  ordinary : ScalarAdjunction l S Y X (fun E ↦ AdicExceptionalProjection.pull l E f)
    (fun E ↦ (O E).direct) (fun E ↦ (O E).ordinary) pull direct
  shriek : ScalarAdjunction l S X Y (fun E ↦ AdicExceptionalProjection.support l E f c)
    (fun E ↦ (O E).exceptional) (fun E ↦ (O E).shriek) support exceptional
  pullNormalization : ∀ (E L : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) (M : C l E Y),
    ((pull.iso E L i).hom.app M).hom =
      (scalarPullbackCompleted l E.carrier L.carrier i (arrow f) M.obj M.property.1
        ((AdicExceptionalProjection.pull l E f).obj M).property.1).hom
  supportNormalization : ∀ (E L : Coefficient.{u} l)
    (i : E.carrier →ₐ[ℚ_[l]] L.carrier) (K : C l E X),
    (pbcDerivedExtend
      (completedCoefficientMap l E.carrier L.carrier i Y.scheme)).map
        ((sfQcqsCompactSupportRealization l E.carrier k
        (Fact.out : IsUnit (l : k)) c).hom.app K) ≫ (S.realization E L i Y).hom.app
            ((AdicExceptionalProjection.support l E f c).obj K) ≫
        ((support.iso E L i).hom.app K).hom =
      (PurCompactSupport.comparison (PurCompactSupport.completedChange l E.carrier L.carrier i)
        c).app K.obj ≫
      (PurCompactSupport.image (PurCompactSupport.completed l L.carrier) c).map
        ((S.realization E L i X).hom.app K) ≫
      (sfQcqsCompactSupportRealization l L.carrier k
        (Fact.out : IsUnit (l : k)) c).hom.app
        ((scalar l E L i X).obj K)

end WeilConjectures.AdicExceptionalProjection
