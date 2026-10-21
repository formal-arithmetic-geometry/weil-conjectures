/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.InverseImagePullbackComparisonDerived
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.Paper.PointProEtaleSectionsExact

/-!
# Composition of finite-level point transports

Source: Deligne, Weil II (1.1.7), printed pp. 150--151; the finite-level refinement
of the proof of blueprint lem-trf-frobenius-operator-compact-description; Stacks
Tags 03CE, 06UM, 015F and 0D6D (blueprint: lem-trf-point-transport-composition).

The helpers spell out the recipe in the statement for each power of the fixed
geometric Frobenius. The positive coefficient exponent is indexed by n + 1.
The composition comparison is expressed in the recorded intrinsic finite-module
presentation, with its ordinary comparison and exact localization comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- The recorded point isomorphism, typed in the existing automorphism group.
This is a direct alias, so its powers use Mathlib's automorphism multiplication.
Source: Deligne, Weil II (1.1.7)
(blueprint: lem-trf-point-transport-composition). -/
abbrev pointFrobeniusAut (D : FiniteFieldDatum.{u}) : Aut (Spec (.of D.k)) :=
  frobeniusPointIso D

/-- The arrow (s,h^r) to the final site object (s,id).
Source: Deligne, Weil II (1.1.7), and Stacks 06UM
(blueprint: lem-trf-point-transport-composition). -/
def pointPowerRestriction (D : FiniteFieldDatum.{u}) (r : ℕ) :
    (proEtaleIsoPostcompose ((pointFrobeniusAut D) ^ r).hom).obj
        (ProEt.mk (𝟙 (Spec (.of D.k)))) ⟶ ProEt.mk (𝟙 (Spec (.of D.k))) :=
  (ProEt.forget (Spec (.of D.k))).preimage
    (Over.homMk ((pointFrobeniusAut D) ^ r).hom)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite sigma chain map is uniquely fixed on every term and section.
Source: Stacks 06UM and 015F; blueprint finite/integral paragraph
(blueprint: lem-trf-point-transport-composition).
Proof: use restriction along h^r and then the distinguished comma coprojection
and the sheafification unit. In the recorded sectionwise inverse-image model the
latter two maps identify the section with itself. Restrictions commute with d.
The constant coefficient comparison fixes every constant section, so restriction
is linear for the transported c inverse action. Equality on all sections proves
uniqueness of the chain map. No naturality in derived morphisms is used. -/
theorem pointPowerFiniteSigma_existsUnique (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ∃! f : ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).obj K ⟶
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).obj
          (((inverseImageFiniteModules l E ((pointFrobeniusAut D) ^ r).hom n).mapHomologicalComplex
               (.up ℤ)).obj K),
      ∀ (i : ℤ) (x : (K.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        f.f i x = (K.X i).val.map (pointPowerRestriction D r).op x := by
  sorry

/-- Sigma is the specified chain map res, ins, sheafification, in its sectionwise model.
Source: Stacks 06UM and 015F; blueprint displayed sigma
(blueprint: lem-trf-point-transport-composition). -/
def pointPowerFiniteSigma (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).obj K ⟶
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).obj
          (((inverseImageFiniteModules l E ((pointFrobeniusAut D) ^ r).hom n).mapHomologicalComplex
               (.up ℤ)).obj K) :=
  Classical.choose (pointPowerFiniteSigma_existsUnique D l E r n K)

/-- The finite arrow Gamma(kappa) after sigma, including localization's comparisons.
Source: Stacks 06UM and 015F; blueprint finite formula
(blueprint: lem-trf-point-transport-composition). -/
def pointPowerTransportFiniteComplex (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K) ⟶
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
          ((finiteDerivedPullback l E n ((pointFrobeniusAut D) ^ r).hom).obj
            (DerivedCategory.Q.obj K)) :=
  (pointFiniteSections D.k
    (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryFactors.hom.app
      K ≫
    DerivedCategory.Q.map (pointPowerFiniteSigma D l E r n K) ≫
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryFactors.inv.app
      (((inverseImageFiniteModules l E ((pointFrobeniusAut D) ^ r).hom n).mapHomologicalComplex
        (.up ℤ)).obj K) ≫
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
        ((inverseImageFiniteModules l E
          ((pointFrobeniusAut D) ^ r).hom n).mapDerivedCategoryFactors.inv.app K ≫
          inverseImagePullbackComparisonFiniteIntrinsic l ((pointFrobeniusAut D) ^ r).hom E
            (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) n K)

/-- Finite transport on any derived object, using the localization's chosen representative.
Source: Stacks 06UM and 015F; blueprint finite formula
(blueprint: lem-trf-point-transport-composition). -/
def pointPowerTransportFinite (r n : ℕ)
    (N : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))) :
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj N ⟶
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
        ((finiteDerivedPullback l E n ((pointFrobeniusAut D) ^ r).hom).obj N) :=
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
      (DerivedCategory.Q.objObjPreimageIso N).inv ≫
    pointPowerTransportFiniteComplex D l hl E r n (DerivedCategory.Q.objPreimage N) ≫
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
      ((finiteDerivedPullback l E n ((pointFrobeniusAut D) ^ r).hom).map
        (DerivedCategory.Q.objObjPreimageIso N).hom)

/-- Restrict the recorded finite pullback to constructible objects, using its recorded
isomorphism-preservation theorem.
Source: Stacks 06UM and 015F; blueprint constructible-pullback paragraph
(blueprint: lem-trf-point-transport-composition). -/
def pointPowerFinitePullback (r n : ℕ) :
    (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).FullSubcategory ⥤
      (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).FullSubcategory :=
  letI := frobeniusPointPrimeInvertible D l hl
  (intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).lift
    ((intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).ι ⋙
        finiteDerivedPullback l E n ((pointFrobeniusAut D) ^ r).hom)
    (fun K ↦ ((isomorphismFiniteDerivedPullback_termwise l E
      ((pointFrobeniusAut D) ^ r).hom n).choose K.obj K.property).1)

/-- The finite component in the actual point-fibre target category.
Source: Stacks 06UM and 015F; blueprint finite point-transport formula
(blueprint: lem-trf-point-transport-composition). -/
def pointPowerTransportFiniteConstructible (r n : ℕ)
    (N : (intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).FullSubcategory) :
    (pointFiniteFibre D l hl E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).obj N ⟶
      (pointFiniteFibre D l hl E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).obj
        ((pointPowerFinitePullback D l hl E r n).obj N) :=
  ObjectProperty.homMk (pointPowerTransportFinite D l hl E r n N.obj)

/-- The unit-normalized identification of the intrinsic finite pullback with the
recorded tensor pullback. Both factors are the existing adjunction comparisons;
no isomorphism is chosen here.
Source: Stacks 03D3 and 0D6D; the recorded finite composition interface
(blueprint: lem-trf-point-transport-composition). -/
def pointPowerPullbackModel (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finiteDerivedPullback l E n f ≅
      proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  Functor.mapDerivedCategoryNatIso
    ((inverseImageFiniteIntrinsicPullbackComparison f
      (Padic.coefficientExtensionRing l E (n + 1))).symm ≪≫
        integralFinitePullbackModel l E f n)

/-- The canonical composition comparison in intrinsic finite-coefficient coordinates.
Use the recorded canonical tensor comparison, conjugated by the existing
unit-normalized changes of presentation. The initial equality is h^(m+1) = h h^m.
Source: Stacks 0D6D, with the normalization of the recorded derived composition lemma
(blueprint: lem-trf-point-transport-composition). -/
def pointPowerPullbackStep (n m : ℕ) :
    finiteDerivedPullback l E n ((pointFrobeniusAut D) ^ (m + 1)).hom ≅
      finiteDerivedPullback l E n ((pointFrobeniusAut D) ^ m).hom ⋙
        finiteDerivedPullback l E n ((pointFrobeniusAut D) ^ 1).hom :=
  eqToIso (congrArg (finiteDerivedPullback l E n)
    (congrArg Iso.hom (pow_succ (pointFrobeniusAut D) m))) ≪≫
    pointPowerPullbackModel l E n
      ((pointFrobeniusAut D).hom ≫ ((pointFrobeniusAut D) ^ m).hom) ≪≫
    integralFiniteCanonicalPullbackComposition l E
      (pointFrobeniusAut D).hom ((pointFrobeniusAut D) ^ m).hom n ≪≫
    Functor.isoWhiskerRight (pointPowerPullbackModel l E n
      ((pointFrobeniusAut D) ^ m).hom).symm _ ≪≫
    Functor.isoWhiskerLeft _ (pointPowerPullbackModel l E n (pointFrobeniusAut D).hom).symm ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (congrArg (finiteDerivedPullback l E n)
      (congrArg Iso.hom (pow_one (pointFrobeniusAut D))))).symm

/-- The inverse canonical comparison, on the bounded constructible subcategory.
Source: Stacks 0D6D and the finite point-transport composition formula
(blueprint: lem-trf-point-transport-composition). -/
def pointPowerComposition (n m : ℕ)
    (N : (intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).FullSubcategory) :
    (pointPowerFinitePullback D l hl E 1 n).obj
        ((pointPowerFinitePullback D l hl E m n).obj N) ⟶
      (pointPowerFinitePullback D l hl E (m + 1) n).obj N :=
  ObjectProperty.homMk ((pointPowerPullbackStep D l E n m).inv.app N.obj)

/-- The explicitly inserted finite point transports compose and are natural in all
bounded constructible derived morphisms.
Source: Deligne, Weil II (1.1.7), printed pp. 150--151; Stacks 03CE, 06UM, 015F,
06YS and 0D6D (blueprint: lem-trf-point-transport-composition).

Proof:
1. Each h^r is an isomorphism. Constant-coefficient pullback and final-object
   evaluation are exact, so their termwise functors preserve quasi-isomorphisms.
   The recorded isomorphism-pullback theorem preserves bounded constructibility.
2. Identify inverse image with restriction through the distinguished initial
   comma index. Its coprojection and sheafification identify the inserted section
   with itself; scalar extension has inverse x tensor a mapping to c^(-1)(a)x.
3. Thus the specified transport becomes precisely restriction along h^r under
   that identification. Restrictions preserve constants and commute with every
   module-sheaf morphism, giving linearity and ordinary naturality.
4. Compare direct and nested initial coprojections. Both return the same section.
   On the module tensor units the comparison sends (x tensor 1) tensor 1 to
   x tensor 1. Constant-section coefficient maps agree by their normalization.
5. Evaluate this comparison at the final object. The restriction composition law
   gives j_(m+1) = T_m j_1 j_m. Apply this degree by degree; ordinary naturality
   makes the arrows chain maps and gives equality of those chain maps.
6. On a flat-term K-flat resolution the comparison is exactly the canonical
   derived pullback comparison of 0D6D. Exactness and naturality across the
   resolution quasi-isomorphism identify it on every representative. Localize
   the chain-map equality and apply exact point evaluation.
7. Naturality for chain maps extends to inverses of quasi-isomorphisms by
   multiplying by their invertible images on both sides, then to composites.
   Every derived morphism is built from these. Restrict to the recorded full
   bounded constructible categories and their point-fibre functor. -/
theorem point_transport_composition (n : ℕ) :
    (∀ (m : ℕ), 1 ≤ m →
      ∀ N : (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).FullSubcategory,
        pointPowerTransportFiniteConstructible D l hl E (m + 1) n N =
          pointPowerTransportFiniteConstructible D l hl E m n N ≫
            pointPowerTransportFiniteConstructible D l hl E 1 n
              ((pointPowerFinitePullback D l hl E m n).obj N) ≫
            (pointFiniteFibre D l hl E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).map
              (pointPowerComposition D l hl E n m N)) ∧
    (∀ (r : ℕ), 1 ≤ r →
      ∀ (N N' : (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).FullSubcategory) (f : N ⟶ N'),
        pointPowerTransportFiniteConstructible D l hl E r n N ≫
            (pointFiniteFibre D l hl E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).map
              ((pointPowerFinitePullback D l hl E r n).map f) =
          (pointFiniteFibre D l hl E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).map f ≫
            pointPowerTransportFiniteConstructible D l hl E r n N') := by
  sorry

end WeilConjectures
