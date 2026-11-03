/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.Compactification.NagataCompactification
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek

/-! # Specified finite dualizing coefficient and realization data

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/lem-coef-finite-dualizing.md, displayed counit-adjoint coefficient
map and proof paragraphs 1--3.

The value below is a canonical package of the ordinary finite coefficient data. Its
public type contains only the ordinary compactification, finite quotient maps, ordinary
exceptional objects and counits, their adjoint transitions, and the exact comparison-site
realization. The normalized-DVR objects and restrictions are deliberately not part of
this package.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

/-- The finite coefficient ring at level `n`, namely the quotient at exponent `n+1`.
Source: `lem-coef-finite-dualizing`. -/
abbrev finiteDualizingDataCoeff (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) : Type (u + 1) :=
  ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))

/-- Finiteness of the level coefficient ring. Source: `lem-coef-finite-dualizing`. -/
noncomputable instance finiteDualizingDataCoeff_finite (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (finiteDualizingDataCoeff l E n) := by
  let _ := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  infer_instance

/-- Finiteness of the unlifted coefficient ring used by finite realization.
Source: `lem-coef-finite-dualizing`. -/
instance finiteDualizingDataUnliftedCoeff_finite (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)

/-- The actual quotient ring map `q_mn : A_m → A_n`. Source: `lem-coef-finite-dualizing`. -/
def finiteDualizingDataQuotient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {m n : ℕ} (h : n ≤ m) :
    finiteDualizingDataCoeff l E m →+* finiteDualizingDataCoeff l E n :=
  RingHom.ulift.{u + 1, u + 1}
    (Ideal.Quotient.factor
      (S := Padic.coefficientExtensionIdeal l E (m + 1))
      (T := Padic.coefficientExtensionIdeal l E (n + 1))
      (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))

/-- The chosen Nagata compactification of the structure morphism.
Source: `thm-nagata-compactification`. -/
def finiteDualizingDataCompactification (D : FiniteFieldDatum.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    Compactification (X ↘ Spec (.of D.k)) :=
  NagataCompactification (X ↘ Spec (.of D.k))

/-- The ordinary etale exceptional object `W_n`.
Source: `thm-amb-etale-exceptional-adjoint` and `lem-coef-finite-dualizing`. -/
def finiteDualizingDataTerm (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] (n : ℕ) :
    Etale.DerivedCategoryModule (finiteDualizingDataCoeff l E n) X :=
  let c := finiteDualizingDataCompactification D X
  letI := c.hasCompactification
  (Etale.rightDerivedUpperShriek (finiteDualizingDataCoeff l E n)
    (X ↘ Spec (.of D.k))).obj
    (Etale.constantComplex (finiteDualizingDataCoeff l E n) (Spec (.of D.k)))

/-- The ordinary compact-support counit `ε_n`.
Source: `thm-amb-etale-exceptional-adjoint`. -/
def finiteDualizingDataCounit (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] (n : ℕ) :
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (finiteDualizingDataCoeff l E n))
      (finiteDualizingDataCompactification D X)).obj
        (finiteDualizingDataTerm D l E X n) ⟶
      Etale.constantComplex (finiteDualizingDataCoeff l E n) (Spec (.of D.k)) :=
  let c := finiteDualizingDataCompactification D X
  letI := c.hasCompactification
  (Etale.rightDerivedUpperShriekAdjunction
    (finiteDualizingDataCoeff l E n) (X ↘ Spec (.of D.k))).counit.app
      (Etale.constantComplex (finiteDualizingDataCoeff l E n) (Spec (.of D.k)))

/-- The ordinary term `W_n` lies in `D+`: the exceptional inverse image of the bounded-below
constant coefficient complex is bounded below.
Source: `lem-sfb-finite-upper-shriek-bounded-below`, applied to the constant coefficient sheaf. -/
theorem finiteDualizingDataTerm_plus (D : FiniteFieldDatum.{u}) (l : ℕ)
    [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] (n : ℕ) :
    _root_.DerivedCategory.TStructure.t.plus (finiteDualizingDataTerm D l E X n) := by
  let c := finiteDualizingDataCompactification D X
  let := c.hasCompactification
  exact Etale.plus_rightDerivedUpperShriek_obj (finiteDualizingDataCoeff l E n)
    (X ↘ Spec (.of D.k)) _
    ⟨0, _root_.DerivedCategory.TStructure.t.isGE_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _) 0⟩

set_option maxHeartbeats 4000000 in
-- reason for change: the derived adjunction's bounded-below universal pair unfolds a large localization term.
/-- The `CoefficientTensorModel` has an explicit fixed scalar-extension object and the
adjunction unit; only the finite-Tor boundedness is postponed.
Source: `lem-fix-compact-support-coefficient-change`. -/
noncomputable def finiteDualizingDataFixedTensorModel
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B} (T : Scheme.{u})
    (K : _root_.DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : _root_.DerivedCategory.TStructure.t.plus
      ((Sheaf.fixedCoefficientDerivedScalarExtension T.smallEtaleTopology φ).obj K.obj)) :
    Etale.CoefficientTensorModel φ T K := by
  let ad := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
  let L : _root_.DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
    ⟨(Sheaf.fixedCoefficientDerivedScalarExtension T.smallEtaleTopology φ).obj K.obj, hK⟩
  exact
    { obj := L
      unit := ObjectProperty.homMk (ad.unit.app K.obj)
      universal := by
        intro N
        convert (ad.homEquiv K.obj N).bijective using 1
        funext g
        exact (ad.homEquiv_unit K.obj N g).symm }

set_option maxHeartbeats 4000000 in
-- reason for change: the exact-single comparison is a large derived-category normalization term.
/-- The scalar-unit map is induced by the lax monoidal unit of exact restriction and the
canonical constant-complex/single-functor identifications.
Source: `lem-pur-derived-change-of-rings`. -/
noncomputable def finiteDualizingDataScalarUnit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    Etale.constantComplex A T ⟶
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategory).obj
        (Etale.constantComplex B T) :=
  (Etale.constantComplexIsoSingleFunctor A T).hom ≫
    (_root_.DerivedCategory.singleFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).map
      (Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology φ)) ≫
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0).inv.app
      (MonoidalCategoryStruct.tensorUnit
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))) ≫
    (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategory.map
      (Etale.constantComplexIsoSingleFunctor B T).inv

-- Compute the fixed left adjoint on a bounded flat representative. This uses the
-- native sheafified extension of scalars, independently of legacy scalar packages.

private theorem finiteDualizingDataFixedScalar_plus_of_finiteTor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (K : Etale.DerivedCategoryModule A T)
    (hK : Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) T K) :
    _root_.DerivedCategory.TStructure.t.plus
      ((Sheaf.fixedCoefficientDerivedScalarExtension T.smallEtaleTopology φ).obj K) := by
  let := φ.toAlgebra
  let F := Sheaf.extendScalars T.smallEtaleTopology φ
  have : F.PreservesKFlatQuasiIso := by
    constructor
    intro P Q hP hQ f hf
    exact CochainComplex.quasiIso_map_of_iso_tensorRight _ _
      (Sheaf.extendScalarsCompRestrictScalarsIso T.smallEtaleTopology A B) f hP hQ
  let ad := (Sheaf.extendScalarsAdjunction T.smallEtaleTopology φ).derivedAdjunction.ofNatIsoRight
    (Sheaf.restrictScalars T.smallEtaleTopology φ).rightDerivedFunctorIsoMapDerivedCategory
  let e := ad.leftAdjointUniq
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
  obtain ⟨a, b, ht⟩ := hK
  obtain ⟨P, hPa, hPb, hP, ⟨eP⟩⟩ :=
    _root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn ht
  have := hPa
  have := hPb
  have hPk := CochainComplex.kFlat_of_bounded_of_flat P a b hP
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat P hPk
  let eQ : F.leftDerivedFunctor.obj (_root_.DerivedCategory.Q.obj P) ≅
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
    asIso (F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P))
  have hplus : _root_.DerivedCategory.TStructure.t.plus
      (_root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
    ⟨a, inferInstance⟩
  exact _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
    (eQ.symm ≪≫ F.leftDerivedFunctor.mapIso eP ≪≫ e.app K) hplus

-- The coefficient exponent is invertible on the base when l differs from p.

private theorem finiteDualizingDataCoeff_invertibleExponent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    HasInvertibleExponent (finiteDualizingDataCoeff l E n) (Spec (.of D.k)) := by
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hv : Padic.coefficientExtensionAbsoluteValue l E (D.p : E) = 1 := by
    have he := spectralNorm_extends (K := Padic l) (L := E) (D.p : Padic l)
    have hn : ‖(D.p : Padic l)‖ = 1 := Padic.norm_natCast_eq_one_iff.2
      ((Nat.coprime_primes (Fact.out : l.Prime) D.prime).2 hl)
    change spectralNorm (Padic l) E (D.p : E) = 1
    simpa only [map_natCast, hn] using he
  have hu : IsUnit (D.p : Padic.coefficientExtensionIntegers l E) := (h.2.2.1 _).2 hv
  have hq : IsUnit (D.p : Padic.coefficientExtensionRing l E (n + 1)) := by
    simpa using hu.map (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))
  have hqu : IsUnit (D.p : finiteDualizingDataCoeff l E n) := by
    exact hq.map ULift.ringEquiv.symm.toRingHom
  let := hqu.invertible
  exact HasInvertibleExponent.spec_of_charP _ D.p

private theorem finiteDualizingDataTerm_ctf
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] (n : ℕ) :
    Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (finiteDualizingDataCoeff l E n)) X
      (finiteDualizingDataTerm D l E X n) := by
  let A := finiteDualizingDataCoeff l E n
  let S := Spec (.of D.k)
  let c := finiteDualizingDataCompactification D X
  let := c.hasCompactification
  let := finiteDualizingDataCoeff_invertibleExponent D l hl E n
  have hunit : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) S
      (𝟙_ _) :=
    ⟨(Etale.DerivedCategory.boundedConstructible _ S).prop_of_iso
        (_root_.DerivedCategory.singleFunctorObjUnitIso _)
        (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0), 0, 0,
      (Etale.DerivedCategory.torAmplitudeIn _ S 0 0).prop_of_iso
        (_root_.DerivedCategory.singleFunctorObjUnitIso _)
        (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
          (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩
  exact Etale.constructibleFiniteTor_rightDerivedUpperShriek A (𝟙 S) (X ↘ S) hunit

/-- The fixed scalar extension of the ordinary term is bounded below at every quotient level.
Source: `lem-fix-compact-support-coefficient-change`. -/
theorem finiteDualizingDataTermFixedScalar_plus
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] {m n : ℕ} (h : n ≤ m) :
    _root_.DerivedCategory.TStructure.t.plus
      ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology
        (finiteDualizingDataQuotient l E h)).obj
        (finiteDualizingDataTerm D l E X m)) := by
  exact finiteDualizingDataFixedScalar_plus_of_finiteTor _ _ _
    (finiteDualizingDataTerm_ctf D l hl E X m).2

/-- The fixed scalar extension of compact support of the ordinary term is bounded below.
Source: `lem-fix-compact-support-coefficient-change`. -/
theorem finiteDualizingDataCompactSupportFixedScalar_plus
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] {m n : ℕ} (h : n ≤ m) :
    _root_.DerivedCategory.TStructure.t.plus
      ((Sheaf.fixedCoefficientDerivedScalarExtension (Spec (.of D.k)).smallEtaleTopology
        (finiteDualizingDataQuotient l E h)).obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} (finiteDualizingDataCoeff l E m))
          (finiteDualizingDataCompactification D X)).obj
          ⟨finiteDualizingDataTerm D l E X m,
            finiteDualizingDataTerm_plus D l E X m⟩).obj) := by
  let A := finiteDualizingDataCoeff l E m
  let S := Spec (.of D.k)
  let c := finiteDualizingDataCompactification D X
  let := c.hasCompactification
  let := finiteDualizingDataCoeff_invertibleExponent D l hl E m
  have hctf := Etale.constructibleFiniteTor_rightDerivedLowerShriek A (𝟙 S) (X ↘ S)
    (finiteDualizingDataTerm_ctf D l hl E X m)
  apply finiteDualizingDataFixedScalar_plus_of_finiteTor
  exact (Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) S).prop_of_iso
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).app
        ⟨finiteDualizingDataTerm D l E X m, finiteDualizingDataTerm_plus D l E X m⟩).symm
    hctf.2

/-- The coefficient mate is the adjoint of inverse compact-support comparison, the scalar
extension of the old counit, and the scalar-unit map.
Source: `lem-coef-finite-dualizing`. -/
noncomputable def finiteDualizingDataComparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] {m n : ℕ} (h : n ≤ m) :
    (Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology
      (finiteDualizingDataQuotient l E h)).obj
        (finiteDualizingDataTerm D l E X m) ⟶ finiteDualizingDataTerm D l E X n :=
  let c := finiteDualizingDataCompactification D X
  letI := c.hasCompactification
  let A := finiteDualizingDataCoeff l E m
  let B := finiteDualizingDataCoeff l E n
  let q := finiteDualizingDataQuotient l E h
  let K : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨finiteDualizingDataTerm D l E X m, finiteDualizingDataTerm_plus D l E X m⟩
  let M := finiteDualizingDataFixedTensorModel (φ := q) X K
    (finiteDualizingDataTermFixedScalar_plus D l hl E X h)
  let Kc := (Etale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} A) c).obj K
  let N := finiteDualizingDataFixedTensorModel (φ := q) (Spec (.of D.k)) Kc
    (finiteDualizingDataCompactSupportFixedScalar_plus D l hl E X h)
  let cmp := Etale.compactSupportCoefficientComparisonPlus c M N
  letI : IsIso cmp := Etale.compactSupportCoefficientComparisonPlus_isIso c M N
  let eB := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} B) c
  let eA := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) c
  let word := eB.inv.app M.obj ≫ (inv cmp).hom ≫
    (Sheaf.fixedCoefficientDerivedScalarExtension
      (Spec (.of D.k)).smallEtaleTopology q).map
      (eA.hom.app K ≫ finiteDualizingDataCounit D l E X m) ≫
    ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Spec (.of D.k)).smallEtaleTopology q)).homEquiv _ _).symm
      (finiteDualizingDataScalarUnit q (Spec (.of D.k)))
  (Etale.rightDerivedUpperShriekAdjunction B
    (X ↘ Spec (.of D.k))).homEquiv _ _ word

/-- Quotient maps are identity maps at equal levels.  This is the representative-level
identity law for the coefficient tower. Source: `lem-coef-finite-dualizing`. -/
theorem finiteDualizingDataQuotient_id (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    finiteDualizingDataQuotient l E (le_refl n) = RingHom.id _ := by
  ext x
  change Ideal.Quotient.factor (le_refl _) x.down = x.down
  simp only [Ideal.Quotient.factor_eq, RingHom.id_apply]

/-- Quotient maps compose on residue representatives. Source: `lem-coef-finite-dualizing`. -/
theorem finiteDualizingDataQuotient_comp (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {r m n : ℕ} (hmr : m ≤ r) (hnm : n ≤ m) :
    finiteDualizingDataQuotient l E (hnm.trans hmr) =
      (finiteDualizingDataQuotient l E hnm).comp
        (finiteDualizingDataQuotient l E hmr) := by
  ext x
  change Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (hnm.trans hmr) 1)) x.down =
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1))
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hmr 1)) x.down)
  exact (Ideal.Quotient.factor_comp_apply _ _ x.down).symm

/-- The unlifted quotient map is the coefficient map seen by the finite pro-etale
realization.  Its `RingHom.ulift` is exactly `finiteDualizingDataQuotient`.
Source: `lem-coef-finite-dualizing`. -/
def finiteDualizingDataUnliftedQuotient
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {m n : ℕ} (h : n ≤ m) :
    Padic.coefficientExtensionRing l E (m + 1) →+* Padic.coefficientExtensionRing l E (n + 1) :=
  Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E (m + 1))
    (T := Padic.coefficientExtensionIdeal l E (n + 1))
    (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The comparison-site scalar-restriction square of the finite realization at the actual
quotient `q_mn`: the canonical sectionwise-identity square `sfRealizationRestriction`
(upstream `sfRealizationRestriction_existsUnique`), along the constant-sheaf image of `q_mn`.
Source: `lem-coef-finite-dualizing`, final sentence of the proof. -/
noncomputable def finiteDualizingDataComparisonSiteScalarRestriction_q
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {m n : ℕ} (h : n ≤ m) (T : Scheme.{u})
    [Finite (Padic.coefficientExtensionRing l E (m + 1))]
    [Finite (Padic.coefficientExtensionRing l E (n + 1))] :=
  AlgebraicGeometry.Scheme.sfRealizationRestriction T
    (finiteDualizingDataUnliftedQuotient l E h)

/-- The semilinear adjunct of the coefficient mate. Source: `lem-coef-finite-dualizing`. -/
def finiteDualizingDataTransition (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] {m n : ℕ} (h : n ≤ m) :
    finiteDualizingDataTerm D l E X m ⟶
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology
        (finiteDualizingDataQuotient l E h)).obj
        (finiteDualizingDataTerm D l E X n) :=
  (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology
      (finiteDualizingDataQuotient l E h))).homEquiv _ _
      (finiteDualizingDataComparison D l hl E X h)

/-- The exact finite realization functor `S_n`, available on every scheme occurring in the
ordinary counit square.
Source: `lem-coef-finite-dualizing`. -/
noncomputable def finiteDualizingDataRealization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (n : ℕ) :
    Etale.DerivedCategoryModule (finiteDualizingDataCoeff l E n) T ⥤
      T.proEtaleDerivedCategory (Padic.coefficientExtensionRing l E (n + 1)) := by
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  exact ProEtale.finiteCoefficientIntrinsicDerivedComparison T
    (Padic.coefficientExtensionRing l E (n + 1))

/-- The transport `S_n(W_n)` of the ordinary dualizing object through the exact finite
realization. Source: `lem-coef-finite-dualizing`, final sentence of the proof. -/
noncomputable def finiteDualizingDataRealizedTerm
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] (n : ℕ) :=
  (finiteDualizingDataRealization l E X n).obj (finiteDualizingDataTerm D l E X n)

/-- The transport `S_n(ε_n)` of the ordinary counit through the level-`n` finite realization on
`Spec k`. Source: `lem-coef-finite-dualizing`, final sentence of the proof. -/
noncomputable def finiteDualizingDataRealizedCounit
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] (n : ℕ) :=
  (finiteDualizingDataRealization l E (Spec (.of D.k)) n).map
    (finiteDualizingDataCounit D l E X n)

/-- The transport `S_n(u_mn)` of the coefficient mate through the finite realization.
Source: `lem-coef-finite-dualizing`, final sentence of the proof. -/
noncomputable def finiteDualizingDataRealizedComparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] {m n : ℕ} (h : n ≤ m) :=
  (finiteDualizingDataRealization l E X n).map
    (finiteDualizingDataComparison D l hl E X h)

/-- The transport `S_m(v_mn)` of the semilinear scalar adjunct through the finite realization.
Source: `lem-coef-finite-dualizing`, final sentence of the proof. -/
noncomputable def finiteDualizingDataRealizedTransition
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] {m n : ℕ} (h : n ≤ m) :=
  (finiteDualizingDataRealization l E X m).map
    (finiteDualizingDataTransition D l hl E X h)

/-- The ordinary finite dualizing coefficient package. Source: `lem-coef-finite-dualizing`. -/
structure FiniteDualizingCoefficientData
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] where
  compactification : Compactification (X ↘ Spec (.of D.k))
  term : ∀ n : ℕ, Etale.DerivedCategoryModule (finiteDualizingDataCoeff l E n) X
  counit : ∀ n : ℕ,
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (finiteDualizingDataCoeff l E n)) compactification).obj
        (term n) ⟶ Etale.constantComplex (finiteDualizingDataCoeff l E n)
          (Spec (.of D.k))
  comparison : ∀ {m n : ℕ} (h : n ≤ m),
    (Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology
      (finiteDualizingDataQuotient l E h)).obj
      (term m) ⟶ term n
  transition : ∀ {m n : ℕ} (h : n ≤ m),
    term m ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology
      (finiteDualizingDataQuotient l E h)).obj (term n)
  realizedTerm : ∀ n : ℕ,
    X.proEtaleDerivedCategory (Padic.coefficientExtensionRing l E (n + 1))
  realizedCounit : ∀ n : ℕ,
    (finiteDualizingDataRealization l E (Spec (.of D.k)) n).obj
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (finiteDualizingDataCoeff l E n)) compactification).obj
          (term n)) ⟶
      (finiteDualizingDataRealization l E (Spec (.of D.k)) n).obj
        (Etale.constantComplex (finiteDualizingDataCoeff l E n) (Spec (.of D.k)))
  realizedComparison : ∀ {m n : ℕ} (h : n ≤ m),
    (finiteDualizingDataRealization l E X n).obj
        ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology
          (finiteDualizingDataQuotient l E h)).obj (term m)) ⟶
      (finiteDualizingDataRealization l E X n).obj (term n)
  realizedTransition : ∀ {m n : ℕ} (h : n ≤ m),
    (finiteDualizingDataRealization l E X m).obj (term m) ⟶
      (finiteDualizingDataRealization l E X m).obj
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
          (finiteDualizingDataQuotient l E h)).obj (term n))
  realization : ∀ n : ℕ,
    ProEtale.FiniteCoefficientEtaleDerivedCategory X
      (finiteDualizingDataCoeff l E n) ⥤
      X.proEtaleDerivedCategory (Padic.coefficientExtensionRing l E (n + 1))

/-- Canonical ordinary finite data and realization.
Blueprint: `def-coef-finite-dualizing-data`; source: `lem-coef-finite-dualizing.md`. -/
noncomputable def finiteDualizingCoefficientData
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    FiniteDualizingCoefficientData D l E X := by
  let c := finiteDualizingDataCompactification D X
  letI := c.hasCompactification
  exact
    { compactification := c
      term := finiteDualizingDataTerm D l E X
      counit := fun n ↦ finiteDualizingDataCounit D l E X n
      comparison := finiteDualizingDataComparison D l hl E X
      transition := finiteDualizingDataTransition D l hl E X
      realizedTerm := finiteDualizingDataRealizedTerm D l E X
      realizedCounit := finiteDualizingDataRealizedCounit D l E X
      realizedComparison := finiteDualizingDataRealizedComparison D l hl E X
      realizedTransition := finiteDualizingDataRealizedTransition D l hl E X
      realization := fun n ↦ by
        letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
        exact ProEtale.finiteCoefficientIntrinsicDerivedComparison X
          (Padic.coefficientExtensionRing l E (n + 1)) }

end WeilConjectures
