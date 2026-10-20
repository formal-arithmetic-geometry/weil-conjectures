/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison
public import Sheaf.Paper.IsomorphismDerivedPullback
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Invertible

/-!
# Point transport along geometric Frobenius

Source: Deligne, Weil II (1.1.7), pp. 150--151; the explicit restriction,
comma-coprojection and sheafification construction in the blueprint
(blueprint: def-weil-frobenius-point-transport).

The canonical sectionwise model of inverse image along an isomorphism identifies
its comma coprojection followed by sheafification with the identity on sections.
Thus sigma is the restriction along g_s in that model. The finite comparison is
the recorded tensor-unit map; the integral comparison is the recorded Roos lift,
not tensor extension by the completed coefficient sheaf. Rational transport is
scalar extension of the integral arrow. The algebraic-closure arrow is represented
at the object's own coefficient stage. No naturality or invertibility is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- Spec of the geometric field Frobenius, with its prescribed inverse.
Source: Deligne, Weil II (1.1.7) (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointIso (D : FiniteFieldDatum.{u}) : Spec (.of D.k) ≅ Spec (.of D.k) :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  Scheme.Spec.mapIso
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingEquiv.toCommRingCatIso.op

/-- The arrow (s,g_s) to (s,id) of the small pro-etale site.
Source: blueprint restriction formula (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointRestriction (D : FiniteFieldDatum.{u}) :
    (proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj
        (ProEt.mk (𝟙 (Spec (.of D.k)))) ⟶ ProEt.mk (𝟙 (Spec (.of D.k))) :=
  (ProEt.forget (Spec (.of D.k))).preimage (Over.homMk (frobeniusPointIso D).hom)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The excluded characteristic makes l a unit in every stalk of s.
Source: finite-field datum and l ≠ p (blueprint: def-weil-frobenius-point-transport).
Proof: Nat.card k₀ = p^a with p prime and a positive implies characteristic p.
The algebraic closure and its local rings have the same characteristic. A prime l
unequal to p has nonzero image there, so is a unit in the field stalk. -/
theorem frobeniusPointPrimeUnit (D : FiniteFieldDatum.{u}) (l : ℕ)
    [Fact l.Prime] (_hl : l ≠ D.p) :
    ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).presheaf.stalk x) := by
  intro x
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hc : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hc
  have hu : IsUnit (l : D.k₀) := (CharP.isUnit_natCast_iff D.prime).2 (by
    intro hdiv
    exact _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 hdiv).symm)
  have hk : IsUnit (l : D.k) := by
    simpa only [map_natCast] using hu.map (algebraMap D.k₀ D.k)
  have h := hk.map
    (StructureSheaf.toStalk (CommRingCat.of D.k) x).hom
  simpa only [map_natCast] using h

/-- The same excluded characteristic makes l a unit in the residue fields.
Source: finite-field datum (blueprint: def-weil-frobenius-point-transport).
Proof: the unique point has residue field canonically k, of characteristic p.
The image of l is nonzero because l and p are distinct primes, hence invertible. -/
theorem frobeniusPointPrimeResidueUnit (D : FiniteFieldDatum.{u}) (l : ℕ)
    [Fact l.Prime] (_hl : l ≠ D.p) :
    ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).residueField x) := by
  intro x
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hc : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hc
  have hu : IsUnit (l : D.k₀) := (CharP.isUnit_natCast_iff D.prime).2 (by
    intro hdiv
    exact _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 hdiv).symm)
  have hk : IsUnit (l : D.k) := by
    simpa only [map_natCast] using hu.map (algebraMap D.k₀ D.k)
  have h := hk.map
    ((StructureSheaf.toStalk (CommRingCat.of D.k) x) ≫ (Spec (.of D.k)).residue x).hom
  simpa only [map_natCast] using h

/-- The canonical inverse of the residue-field unit; no extra hypothesis on s.
Source: finite-field datum (blueprint: def-weil-frobenius-point-transport). -/
@[instance_reducible]
def frobeniusPointPrimeInvertible (x : Spec (.of D.k)) :
    Invertible (l : (Spec (.of D.k)).residueField x) :=
  (frobeniusPointPrimeResidueUnit D l hl x).invertible

/-- The finite sigma chain map is uniquely fixed on every term and section.
Source: blueprint finite/integral paragraph (blueprint: def-weil-frobenius-point-transport).
Proof: use restriction along g_s and then the distinguished comma coprojection
and the sheafification unit. In the recorded sectionwise inverse-image model the
latter two maps identify the section with itself. Restrictions commute with d.
The constant coefficient comparison fixes every constant section, so restriction
is linear for the transported c inverse action. Equality on all sections proves
uniqueness of the chain map. No naturality in derived morphisms is used. -/
theorem frobeniusPointFiniteSigma_existsUnique (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ∃! f : ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).obj K ⟶
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).obj
          (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
               (.up ℤ)).obj K),
      ∀ (i : ℤ) (x : (K.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        f.f i x = (K.X i).val.map (frobeniusPointRestriction D).op x := by
  sorry

/-- Sigma is the specified chain map res, ins, sheafification, in its sectionwise model.
Source: blueprint displayed sigma (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointFiniteSigma (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).obj K ⟶
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
      (.up ℤ)).obj
          (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
               (.up ℤ)).obj K) :=
  Classical.choose (frobeniusPointFiniteSigma_existsUnique D l E n K)

/-- The integral sigma chain map is fixed on every term and section, with completed action.
Source: blueprint integral paragraph (blueprint: def-weil-frobenius-point-transport).
Proof: use the same restriction and comma generator as at finite level. The limit
coefficient comparison is compatible with every quotient projection. Constant
integral sections are the compatible constant reductions, hence it fixes them.
Restriction is therefore O_E-linear for the completed action. Restrictions commute
with differentials, and equality on all term sections gives uniqueness. -/
theorem frobeniusPointIntegralSigma_existsUnique
    (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ∃! f : ((pointIntegralSections l E D.k).mapHomologicalComplex
      (.up ℤ)).obj K ⟶
        ((pointIntegralSections l E D.k).mapHomologicalComplex
      (.up ℤ)).obj
          (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
               (.up ℤ)).obj K),
      ∀ (i : ℤ) (x : (K.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        f.f i x = (K.X i).val.map (frobeniusPointRestriction D).op x := by
  sorry

/-- Integral sigma, with its completed coefficient action fixed by all quotient maps.
Source: blueprint displayed sigma (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointIntegralSigma
    (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ((pointIntegralSections l E D.k).mapHomologicalComplex
      (.up ℤ)).obj K ⟶
        ((pointIntegralSections l E D.k).mapHomologicalComplex
      (.up ℤ)).obj
          (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
               (.up ℤ)).obj K) :=
  Classical.choose (frobeniusPointIntegralSigma_existsUnique D l E K)

/-- The finite arrow Gamma(kappa) after sigma, including localization's comparisons.
Source: blueprint finite formula (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointTransportFiniteComplex (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K) ⟶
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
          ((finiteDerivedPullback l E n (frobeniusPointIso D).hom).obj
            (DerivedCategory.Q.obj K)) :=
  (pointFiniteSections D.k
    (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryFactors.hom.app
      K ≫
    DerivedCategory.Q.map (frobeniusPointFiniteSigma D l E n K) ≫
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryFactors.inv.app
      (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
        (.up ℤ)).obj K) ≫
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
        ((inverseImageFiniteModules l E
          (frobeniusPointIso D).hom n).mapDerivedCategoryFactors.inv.app K ≫
          inverseImagePullbackComparisonFiniteIntrinsic l (frobeniusPointIso D).hom E
            (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) n K)

/-- The integral arrow uses the recorded resolution and map into the strict derived limit.
Source: blueprint integral formula (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointTransportIntegralComplex
    (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : P.obj ⟶ K) [QuasiIso q] :
    (pointFibreIntegralAmbient D l E).obj (DerivedCategory.Q.obj K) ⟶
      (pointFibreIntegralAmbient D l E).obj
        ((integralDerivedPullback l E (frobeniusPointIso D).hom).obj
          (DerivedCategory.Q.obj K)) :=
  (pointIntegralSections l E D.k).mapDerivedCategoryFactors.hom.app K ≫
    DerivedCategory.Q.map (frobeniusPointIntegralSigma D l E K) ≫
    (pointIntegralSections l E D.k).mapDerivedCategoryFactors.inv.app
      (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
        (.up ℤ)).obj K) ≫
    (pointFibreIntegralAmbient D l E).map
      ((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapDerivedCategoryFactors.inv.app
          K ≫
        inverseImagePullbackComparison l E (frobeniusPointIso D).hom
          (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) K P q)


/-- Finite transport on any derived object, using the localization's chosen representative.
Source: blueprint finite formula (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointTransportFinite (n : ℕ)
    (N : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))) :
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj N ⟶
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
        ((finiteDerivedPullback l E n (frobeniusPointIso D).hom).obj N) :=
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
      (DerivedCategory.Q.objObjPreimageIso N).inv ≫
    frobeniusPointTransportFiniteComplex D l hl E n (DerivedCategory.Q.objPreimage N) ≫
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
      ((finiteDerivedPullback l E n (frobeniusPointIso D).hom).map
        (DerivedCategory.Q.objObjPreimageIso N).hom)

/-- The integral arrow is uniquely specified by the explicit formula on resolutions.
This is well-definedness of the component, not naturality of a family of components.
Source: blueprint integral formula and its fixed-resolution convention
(blueprint: def-weil-frobenius-point-transport).
Proof: represent N by a complex K and take its K-flat resolution with flat terms.
Use frobeniusPointTransportIntegralComplex and conjugate by the representing
isomorphism. For two resolutions take a common K-flat refinement. Restrictions,
finite reductions and their tensor units commute with the refinement, hence so
do their compatible products and the zero-homotopy Roos lift. Inverting the two
resolution quasi-isomorphisms gives equal arrows. The same localization argument
handles a change of complex representative. Thus the formula holds for every
representative and resolution; one such representative determines the arrow uniquely.
No invertibility of kappa on arbitrary objects or natural transformation is assumed. -/
theorem frobeniusPointTransportIntegral_existsUnique
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :
    ∃! f : (pointFibreIntegralAmbient D l E).obj N ⟶
        (pointFibreIntegralAmbient D l E).obj
          ((integralDerivedPullback l E (frobeniusPointIso D).hom).obj N),
      ∀ (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
        (q : P.obj ⟶ K) [QuasiIso q] (e : DerivedCategory.Q.obj K ≅ N),
        f = (pointFibreIntegralAmbient D l E).map e.inv ≫
          frobeniusPointTransportIntegralComplex D l hl E K P q ≫
          (pointFibreIntegralAmbient D l E).map
            ((integralDerivedPullback l E (frobeniusPointIso D).hom).map e.hom) := by
  sorry

/-- Integral point transport, fixed uniquely by its restriction and Roos-resolution formula.
Source: blueprint integral formula (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointTransportIntegral
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :
    (pointFibreIntegralAmbient D l E).obj N ⟶
      (pointFibreIntegralAmbient D l E).obj
        ((integralDerivedPullback l E (frobeniusPointIso D).hom).obj N) :=
  Classical.choose (frobeniusPointTransportIntegral_existsUnique D l hl E N)

/-- The actual constructible integral pullback, with l-invertibility derived from l ≠ p.
Source: blueprint constructible-pullback paragraph
(blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointIntegralPullback :
    sfIntegralConstructibleCategory l E (Spec (.of D.k)) ⥤
      sfIntegralConstructibleCategory l E (Spec (.of D.k)) :=
  letI := frobeniusPointPrimeInvertible D l hl
  constructibleIntegralPullback l E (frobeniusPointIso D).hom

/-- Restrict the recorded finite pullback to constructible objects, using its recorded
isomorphism-preservation theorem.
Source: blueprint constructible-pullback paragraph
(blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointFinitePullback (n : ℕ) :
    (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).FullSubcategory ⥤
      (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).FullSubcategory :=
  letI := frobeniusPointPrimeInvertible D l hl
  (intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).lift
    ((intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).ι ⋙
        finiteDerivedPullback l E n (frobeniusPointIso D).hom)
    (fun K ↦ ((isomorphismFiniteDerivedPullback_termwise l E
      (frobeniusPointIso D).hom n).choose K.obj K.property).1)

/-- The finite component in the actual point-fibre target category.
Source: blueprint finite point-transport formula
(blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointTransportFiniteConstructible (n : ℕ)
    (N : (intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).FullSubcategory) :
    (pointFiniteFibre D l hl E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).obj N ⟶
      (pointFiniteFibre D l hl E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).obj
        ((frobeniusPointFinitePullback D l hl E n).obj N) :=
  ObjectProperty.homMk (frobeniusPointTransportFinite D l hl E n N.obj)

/-- The integral component in the actual finitely generated complete point-fibre category.
Source: blueprint integral point-transport formula
(blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointTransportIntegralConstructible
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (pointIntegralFibre D l hl E).obj N ⟶
      (pointIntegralFibre D l hl E).obj ((frobeniusPointIntegralPullback D l hl E).obj N) :=
  ObjectProperty.homMk (frobeniusPointTransportIntegral D l hl E N.obj)

/-- The rational pullback object is the same integral pullback object in raw rationalization.
Source: blueprint rational paragraph (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointRationalPullbackObj
    (N : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    sfRationalConstructibleCategory l E (Spec (.of D.k)) :=
  ⟨(frobeniusPointIntegralPullback D l hl E).obj N.obj⟩

/-- Rational transport is exactly tensor with E of the integral arrow. The only additional
arrows are the recorded coefficient-size descent and rational-object identifications.
Source: blueprint rational formula (blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointTransportRational
    (N : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (pointRationalFibre D l hl E).obj N ⟶
      (pointRationalFibre D l hl E).obj (frobeniusPointRationalPullbackObj D l hl E N) :=
  let f : pointFibreRationalLarge D l hl E N.obj ⟶
      pointFibreRationalLarge D l hl E
        ((frobeniusPointIntegralPullback D l hl E).obj N.obj) :=
    ObjectProperty.homMk
      ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategory.map
          (frobeniusPointTransportIntegral D l hl E N.obj.obj))
  (pointRationalFibreObjIso D l hl E N).hom ≫
    (pointFibreSizeDescent E).map f ≫
    (pointRationalFibreObjIso D l hl E (frobeniusPointRationalPullbackObj D l hl E N)).inv

variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The algebraic-closure pullback object retains the actual coefficient stage.
Source: blueprint algebraic-closure paragraph
(blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointQbarPullbackObj
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)) :=
  ⟨N.stage, frobeniusPointRationalPullbackObj D l hl
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N.stage) N.obj⟩

/-- The point transport at Qbar is represented at precisely the object's own stage E'.
The Shrink algebra equivalence is the recorded coefficient-model identification.
Source: blueprint algebraic-closure formula
(blueprint: def-weil-frobenius-point-transport). -/
def frobeniusPointTransportQbar
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    pointQbarFibreObj D l hl Ω N ⟶
      pointQbarFibreObj D l hl Ω (frobeniusPointQbarPullbackObj D l hl Ω N) :=
  (DerivedCategory.pointFdQbarStage l Ω N.stage).map
    ((DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] N.stage.val :
        AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N.stage ≃ₐ[ℚ_[l]]
          N.stage.val).toRingHom).map
      (frobeniusPointTransportRational D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N.stage) N.obj))

end WeilConjectures
