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
import Sheaf.Paper.IntegralPullbackReductionCounit

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
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u v w
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

attribute [local irreducible] frobeniusPointIso frobeniusPointRestriction

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

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem pointFiniteScalar_restriction (n : ℕ)
    (a : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) :
    (inv (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n)).hom.app
        (op (ProEt.mk (𝟙 (Spec (.of D.k)))))
        (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1)) a) =
      (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.map
        (frobeniusPointRestriction D).op
        (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1)) a) := by
  let A := CommRingCat.of
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
  let U := ProEt.mk (𝟙 (Spec (.of D.k)))
  let c := inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n
  have hn := (isoSectionwiseConstantMap_existsUnique.{u, u}
    (frobeniusPointIso D).hom A).exists.choose_spec U a
  have hr := congrArg (fun f ↦ f a)
    ((toSheafify (ProEt.topology (Spec (.of D.k)))
      ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj A)).naturality
        (frobeniusPointRestriction D).op)
  have hi := congrArg (fun f ↦ f.hom.app (op U)
    ((toSheafify (ProEt.topology (Spec (.of D.k)))
      ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj A)).app
        (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U)) a))
    (IsIso.hom_inv_id c)
  have hh := congrArg (fun x ↦ (inv c).hom.app (op U) x) hn
  change _ = (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.map
    (frobeniusPointRestriction D).op (pointConstantSectionMap D.k _ a) at hr
  change _ = (inv c).hom.app (op U) (pointConstantSectionMap D.k _ a) at hh
  change _ = _ at hi
  exact hh.symm.trans (hi.trans hr)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private def sectionRestrictionLinear
    {C : Type v} [Category.{w} C] {R : Cᵒᵖ ⥤ RingCat.{u + 1}}
    (M : PresheafOfModules.{u + 1} R) {U V : Cᵒᵖ} (r : U ⟶ V)
    {A : Type (u + 1)} [Ring A] (a : A →+* R.obj U) (b : R.obj U →+* R.obj V)
    (h : ∀ c, R.map r (a c) = b (a c)) :
    (ModuleCat.restrictScalars a).obj (M.obj U) ⟶
      (ModuleCat.restrictScalars a).obj ((ModuleCat.restrictScalars b).obj (M.obj V)) := by
  refine ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars a).obj (M.obj U))
    (Y := (ModuleCat.restrictScalars a).obj ((ModuleCat.restrictScalars b).obj (M.obj V)))
    { toFun := fun x ↦ M.map r x
      map_add' := fun x y ↦ (M.map r).hom.map_add x y
      map_smul' := ?_ }
  intro c x
  exact (M.map_smul r (a c) x).trans
    (congrArg (fun d ↦ @SMul.smul _ _ (M.obj V).isModule.toSMul d (M.map r x)) (h c))

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private def pointFiniteSigmaTerm (n : ℕ)
    (M : integralOperationsFiniteModules l E (Spec (.of D.k)) n) :
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).obj M ⟶
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).obj
        ((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).obj M) := by
  exact sectionRestrictionLinear M.val (frobeniusPointRestriction D).op
    (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1)))
    ((inv (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n)).hom.app
      (op (ProEt.mk (𝟙 (Spec (.of D.k)))))).hom
    (fun a ↦ (pointFiniteScalar_restriction D l E n a).symm)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
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
      ∀ i : ℤ, HEq (fun x ↦ f.f i x)
        (fun x ↦ (K.X i).val.map (frobeniusPointRestriction D).op x) := by
  let f : ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).obj
        (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
          (.up ℤ)).obj K) :=
    { f i := pointFiniteSigmaTerm D l E n (K.X i)
      comm' i j _ := by
        ext x
        exact (PresheafOfModules.naturality_apply (K.d i j).val
          (frobeniusPointRestriction D).op x) }
  refine ⟨f, fun _ ↦ HEq.rfl, ?_⟩
  intro g hg
  apply HomologicalComplex.hom_ext
  intro i
  ext x
  exact congrFun (eq_of_heq (hg i)) x

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

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem pointIntegralScalar_projection (n : ℕ)
    (a : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) :
    (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n)).hom.app
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) (pointIntegralSectionMap l E D.k a) =
      pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1))
        (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a.down)) := by
  let Y := Spec (.of D.k)
  let U := op (ProEt.mk (𝟙 Y))
  let A := CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
  let B := CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
  let q : A ⟶ B := CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
        (ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).toRingHom))
  have hp := congrArg (fun f ↦ f.hom.app U (pointConstantSectionMap D.k _ a))
    (limit.lift_π (integralConstantCoefficientCone l E Y) (op n))
  change _ = (integralConstantQuotientRingMap l E Y n).hom.app U
    (pointConstantSectionMap D.k _ a) at hp
  have hn := congrArg (fun f ↦ (f.app U).hom a)
    (toSheafify_naturality (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).map q))
  exact hp.trans hn.symm

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem pointIntegralScalar_restriction
    (a : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) :
    (inv (inverseImageCompletedCoefficientMap l E (frobeniusPointIso D).hom)).hom.app
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) (pointIntegralSectionMap l E D.k a) =
      (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))).obj.map
        (frobeniusPointRestriction D).op (pointIntegralSectionMap l E D.k a) := by
  let Y := Spec (.of D.k)
  let U := op (ProEt.mk (𝟙 Y))
  let R := integralCoefficientSheafSystem l E Y
  let c := inverseImageCompletedCoefficientMap l E (frobeniusPointIso D).hom
  let r := frobeniusPointRestriction D
  let x := pointIntegralSectionMap l E D.k a
  have hc : c.hom.app U
      ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map r.op x) = x := by
    let ev := sheafToPresheaf (ProEt.topology Y) RingCat.{u + 1} ⋙
      (evaluation Y.ProEtᵒᵖ RingCat.{u + 1}).obj U
    apply Concrete.isLimit_ext (R ⋙ ev) (isLimitOfPreserves ev (limit.isLimit R))
    intro j
    obtain ⟨n⟩ := j
    have heq : c ≫ limit.π R (op n) =
        inverseImageCompletedCoefficientComponent l E (frobeniusPointIso D).hom n :=
      limit.lift_π _ _
    have hp := congrArg (fun f ↦ f.hom.app U
      ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map r.op x)) heq
    change (limit.π R (op n)).hom.app U (c.hom.app U
      ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map r.op x)) = _ at hp
    change (limit.π R (op n)).hom.app U (c.hom.app U
      ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map r.op x)) = _
    rw [hp]
    change (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n).hom.app U
      ((limit.π R (op n)).hom.app _
        ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map r.op x)) = _
    have hnat := congrArg (fun f ↦ f x) ((limit.π R (op n)).hom.naturality r.op)
    change (limit.π R (op n)).hom.app _
      ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map r.op x) = _ at hnat
    erw [hnat]
    change (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n).hom.app U
      ((R.obj (op n)).obj.map r.op
        ((limit.π R (op n)).hom.app U (pointIntegralSectionMap l E D.k a))) =
      (limit.π R (op n)).hom.app U (pointIntegralSectionMap l E D.k a)
    erw [pointIntegralScalar_projection D l E n a]
    erw [← pointFiniteScalar_restriction D l E n]
    have hi := congrArg (fun f ↦ f.hom.app U
      (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1))
        (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a.down))))
      (IsIso.inv_hom_id (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n))
    exact hi
  have hi := congrArg (fun f ↦ f.hom.app U
    ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map r.op x))
    (IsIso.hom_inv_id c)
  exact (congrArg (fun y ↦ (inv c).hom.app U y) hc).symm.trans hi

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private def pointIntegralSigmaTerm
    (M : integralTowerModules l E (Spec (.of D.k))) :
    (pointIntegralSections l E D.k).obj M ⟶
      (pointIntegralSections l E D.k).obj
        ((inverseImageIntegralModules l E (frobeniusPointIso D).hom).obj M) := by
  exact sectionRestrictionLinear M.val (frobeniusPointRestriction D).op
    (pointIntegralSectionMap l E D.k)
    ((inv (inverseImageCompletedCoefficientMap l E (frobeniusPointIso D).hom)).hom.app
      (op (ProEt.mk (𝟙 (Spec (.of D.k)))))).hom
    (fun a ↦ (pointIntegralScalar_restriction D l E a).symm)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
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
      ∀ i : ℤ, HEq (fun x ↦ f.f i x)
        (fun x ↦ (K.X i).val.map (frobeniusPointRestriction D).op x) := by
  let f : ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
        (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
          (.up ℤ)).obj K) :=
    { f i := pointIntegralSigmaTerm D l E (K.X i)
      comm' i j _ := by
        ext x
        exact (PresheafOfModules.naturality_apply (K.d i j).val
          (frobeniusPointRestriction D).op x) }
  refine ⟨f, fun _ ↦ HEq.rfl, ?_⟩
  intro g hg
  apply HomologicalComplex.hom_ext
  intro i
  ext x
  exact congrFun (eq_of_heq (hg i)) x

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

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private def pointIntegralComparison
    (C : IntegralComparisonCoefficientData l E) :
    inverseImageIntegralDerived l E (frobeniusPointIso D).hom ⟶
      integralDerivedPullback l E (frobeniusPointIso D).hom := by
  let Y := Spec (.of D.k)
  let g := (frobeniusPointIso D).hom
  let H := inverseImageIntegralDerived l E g
  let Δ := integralComparisonConstantTower l E Y
  let U := coefficientSequenceDerivedRestriction l E Y
  let B := integralComparisonDerivedSequencePullback l E g
  let S := C.system Y
  let d : Δ ⟶ S.reduction ⋙ U :=
    Functor.whiskerRight S.adjunction.unit Δ ≫
      Functor.whiskerLeft (S.reduction ⋙ U) (integralComparisonTowerCounit l E Y)
  let β : H ⋙ Δ ⟶ S.reduction ⋙ B ⋙ U :=
    (integralTowerInverseImageDiagonal l E g).hom ≫
      Functor.whiskerRight d (integralDerivedTowerInverseImage l E g) ≫
      Functor.whiskerLeft S.reduction (integralDerivedTowerInverseImageUnit l E g).hom
  let τ : H ⟶ S.reduction ⋙ B ⋙ coefficientSequenceLimit l E Y :=
    { app N := (integralComparisonConstantAdjunction l E Y).homEquiv _ _ (β.app N)
      naturality := by
        intro N M f
        exact (Adjunction.homEquiv_naturality_left_square
          (integralComparisonConstantAdjunction l E Y) (H.map f)
          (β.app M) (β.app N) ((S.reduction ⋙ B ⋙ U).map f)
          (β.naturality f)) }
  exact τ ≫ (C.pullback g).realization.inv

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem pointIntegralComparison_good
    (C : IntegralComparisonCoefficientData l E)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) :
    (pointIntegralComparison D l E C).app (DerivedCategory.Q.obj P.obj) =
      (inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapDerivedCategoryFactors.hom.app
          P.obj ≫
        DerivedCategory.Q.map
          (inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P.obj) ≫
        (integralDerivedPullbackComparison l E (frobeniusPointIso D).hom).inv.app P := by
  let Y := Spec (.of D.k)
  let g := (frobeniusPointIso D).hom
  let F := C.pullback g
  let S := C.system Y
  let a := (inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.app P.obj ≫
    DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E g P.obj) ≫
    (integralDerivedPullbackComparison l E g).inv.app P
  apply (cancel_mono (F.realization.hom.app (DerivedCategory.Q.obj P.obj))).1
  change _ = a ≫ F.realization.hom.app (DerivedCategory.Q.obj P.obj)
  dsimp only [pointIntegralComparison, NatTrans.comp_app]
  rw [Category.assoc, F.realization.inv_hom_id_app, Category.comp_id]
  apply (integralComparisonConstantAdjunction l E Y).homEquiv _ _ |>.symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.map_comp, Functor.comp_obj, Functor.id_obj,
    Category.assoc, a, Y, g, F, S, integralComparisonTowerCounit] using
    (integralPullbackKFlatReductionCounit l E g S (C.roos Y) F P).symm

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem pointIntegralComparison_resolution
    (C : IntegralComparisonCoefficientData l E)
    (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : P.obj ⟶ K) [QuasiIso q] :
    (pointIntegralComparison D l E C).app (DerivedCategory.Q.obj K) =
      inverseImagePullbackComparison l E (frobeniusPointIso D).hom
        (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) K P q := by
  let H := inverseImageIntegralDerived l E (frobeniusPointIso D).hom
  apply (cancel_epi (H.map (DerivedCategory.Q.map q))).1
  rw [(pointIntegralComparison D l E C).naturality, pointIntegralComparison_good]
  simp only [inverseImagePullbackComparison, Category.assoc]
  erw [← Category.assoc (H.map (DerivedCategory.Q.map q)),
    (inverseImageIntegralModules l E
      (frobeniusPointIso D).hom).mapDerivedCategoryFactors.hom.naturality q]
  simp only [Functor.comp_map, Category.assoc, IsIso.hom_inv_id_assoc]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
/-- The integral arrow is uniquely specified by the explicit formula on resolutions.
This is well-definedness of the component, not naturality of a family of components.
Source: blueprint integral formula and its fixed-resolution convention
(blueprint: def-weil-frobenius-point-transport).
Proof: represent N by a complex K and take its K-flat resolution with flat terms.
Descend the natural sectionwise sigma through localization at quasi-isomorphisms.
Transpose the whole-tower reduction unit and inverse-image unit under the
constant-tower/derived-limit adjunction. The reduction-counit identity identifies
this natural comparison on each good complex with the prescribed Roos comparison.
Naturality along the resolution quasi-isomorphism gives exactly the comparison
used by frobeniusPointTransportIntegralComplex. Compose with descended sigma and
conjugate by each representing isomorphism to obtain the displayed formula.
One representative and its flat-term K-flat resolution force uniqueness. No
invertibility of the comparison on arbitrary objects is used. -/
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
  obtain ⟨R, _⟩ := integralPullbackComparisonRealization l E E (AlgHom.id ℚ_[l] E)
  let C := R.coefficient E
  let S := pointIntegralSections l E D.k
  let H := inverseImageIntegralModules l E (frobeniusPointIso D).hom
  let Sc := S.mapHomologicalComplex (.up ℤ)
  let Hc := H.mapHomologicalComplex (.up ℤ)
  let Sd := S.mapDerivedCategory
  let Hd := H.mapDerivedCategory
  let T := integralDerivedPullback l E (frobeniusPointIso D).hom
  let σc : Sc ⟶ Hc ⋙ Sc :=
    { app K := frobeniusPointIntegralSigma D l E K
      naturality := by
        intro K L f
        apply HomologicalComplex.hom_ext
        intro i
        ext x
        change (frobeniusPointIntegralSigma D l E L).f i ((f.f i).val.app _ x) =
          ((f.f i).val.app
            (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj
              (ProEt.mk (𝟙 (Spec (.of D.k))))))
            ((frobeniusPointIntegralSigma D l E K).f i x))
        erw [congrFun (eq_of_heq
          ((frobeniusPointIntegralSigma_existsUnique D l E L).choose_spec.1 i)),
          congrFun (eq_of_heq
            ((frobeniusPointIntegralSigma_existsUnique D l E K).choose_spec.1 i))]
        exact (PresheafOfModules.naturality_apply (f.f i).val
          (frobeniusPointRestriction D).op x).symm }
  let σQ : DerivedCategory.Q ⋙ Sd ⟶ DerivedCategory.Q ⋙ Hd ⋙ Sd :=
    S.mapDerivedCategoryFactors.hom ≫ Functor.whiskerRight σc DerivedCategory.Q ≫
      Functor.whiskerLeft Hc S.mapDerivedCategoryFactors.inv ≫
      Functor.whiskerRight H.mapDerivedCategoryFactors.inv Sd
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (integralTowerModules l E (Spec (.of D.k))) (.up ℤ))
    (DerivedCategory (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))
  let σ : Sd ⟶ Hd ⋙ Sd := ff.preimage σQ
  have hσ (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
      σ.app (DerivedCategory.Q.obj K) = σQ.app K :=
    congrArg (fun t ↦ t.app K) (ff.map_preimage σQ)
  let τ : Sd ⟶ T ⋙ Sd :=
    σ ≫ Functor.whiskerRight (pointIntegralComparison D l E C) Sd
  have hτ (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (q : P.obj ⟶ K) [QuasiIso q] :
      τ.app (DerivedCategory.Q.obj K) =
        frobeniusPointTransportIntegralComplex D l hl E K P q := by
    dsimp only [τ, NatTrans.comp_app, Functor.whiskerRight_app]
    rw [hσ, pointIntegralComparison_resolution D l hl E C K P q]
    simp only [σQ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc]
    simp only [frobeniusPointTransportIntegralComplex, Functor.map_comp]
    rfl
  have hformula (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (q : P.obj ⟶ K) [QuasiIso q] (e : DerivedCategory.Q.obj K ≅ N) :
      τ.app N = Sd.map e.inv ≫
        frobeniusPointTransportIntegralComplex D l hl E K P q ≫ Sd.map (T.map e.hom) := by
    rw [← hτ K P q]
    apply (cancel_epi (Sd.map e.hom)).1
    simp only [← Category.assoc, ← Sd.map_comp, e.hom_inv_id, Sd.map_id, Category.id_comp]
    exact τ.naturality e.hom
  refine ⟨τ.app N, hformula, ?_⟩
  intro f hf
  let K := DerivedCategory.Q.objPreimage N
  let e := DerivedCategory.Q.objObjPreimageIso N
  obtain ⟨P, q, hP, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) K
  let := hq
  let P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory :=
    ⟨P, hP, fun i ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso _ (P.X i)).symm (hflat i)⟩
  exact (hf K P' q e).trans (hformula K P' q e).symm

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
