/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.SelectedSchemeGaloisComparison
public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.TraceFormulaCoefficientConventions.TraceFormulaCoefficientConventions
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobenius
public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.AlgebraicGeometry.SixFunctors.FrobeniusTrivializationPullback
public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatRingedToposPullback
import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusFactorization
import WeilConjectures.AlgebraicGeometry.Finite.FiniteIntrinsicPullbackUnitComposition

/-! # Scheme identities and inverse restrictions for finite return Frobenius

Source: finite-field return, absolute Frobenius naturality, and inverse-power cancellation
(blueprint: lem-trf-finite-return-scheme-identities).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option compiler.extract_closed false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.TraceFormulaCoefficientConventions

private theorem returnPositivePower_eq {X : Scheme.{u}} (f : X ⟶ X) (n : ℕ) :
    localPositivePower f n = (End.of f) ^ (n + 1) := by
  induction n with
  | zero => simp [localPositivePower]
  | succ n ih =>
    rw [localPositivePower, ih, pow_succ' (End.of f) (n + 1)]
    rfl

/-- Absolute Frobenius iterates commute with every scheme morphism.
Source: absolute Frobenius on section rings
(blueprint: lem-trf-finite-return-scheme-identities).
Proof: underlying maps are identities. On every open, both structure-sheaf maps agree
because the section ring homomorphism preserves the indicated p-power. -/
theorem returnAbsolute_naturality (T : TraceFormulaCoefficientConventions.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : X ⟶ Spec (.of T.datum.k₀)) (b : Y ⟶ Spec (.of T.datum.k₀)) (m : ℕ) :
    T.returnAbsolute a m ≫ f = f ≫ T.returnAbsolute b m := by
  apply Scheme.Hom.ext (by ext x; rfl)
  intro U
  simp only [Scheme.Hom.comp_app]
  change f.app U ≫ (T.returnAbsolute a m).app (f ⁻¹ᵁ U) ≫
    X.presheaf.map (𝟙 _) = (T.returnAbsolute b m).app U ≫ f.app U
  rw [X.presheaf.map_id, Category.comp_id]
  ext s
  change ((f.app U).hom s) ^ T.datum.p ^ (T.datum.a * m) =
    (f.app U).hom (s ^ T.datum.p ^ (T.datum.a * m))
  exact (map_pow (f.app U).hom s _).symm

private theorem returnAbsolutePoint_eq (T : TraceFormulaCoefficientConventions.{u})
    (m : ℕ) :
    T.returnAbsolute (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m =
      HPow.hPow (α := End (Spec (.of T.datum.k))) (frobeniusPointIso T.datum).inv m := by
  let D := T.datum
  let := Fintype.ofFinite D.k₀
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k
  have hone : (frobeniusPointIso D).inv = Spec.map (CommRingCat.ofHom σ.toRingHom) := by
    simp only [frobeniusPointIso, FiniteField.geometricFrobeniusAlgEquivOfAlgebraic,
      AlgEquiv.aut_inv]
    rfl
  have hpow : HPow.hPow (α := End (Spec (.of D.k))) (frobeniusPointIso D).inv m =
      Spec.map (CommRingCat.ofHom (σ ^ m).toRingHom) := by
    induction m with
    | zero => exact (Spec.map_id _).symm
    | succ m ih =>
      rw [pow_succ', End.mul_def, ih, hone, ← Spec.map_comp]
      congr 1
  change T.returnAbsolute
      (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m = _
  rw [hpow]
  apply AlgebraicGeometry.ext_to_Spec
  change (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
      (T.returnAbsolute
      (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m).appTop =
    (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
      (Spec.map (CommRingCat.ofHom (σ ^ m).toRingHom)).appTop
  rw [← Scheme.ΓSpecIso_inv_naturality]
  ext x
  change ((Scheme.ΓSpecIso (CommRingCat.of D.k)).inv x) ^ D.p ^ (D.a * m) =
    (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ((σ ^ m) x)
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
    ← map_pow, ← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq, pow_mul]

private theorem iso_power_inverse {X : Scheme.{u}} (e : X ≅ X) (m : ℕ) :
    ((End.of e.inv) ^ m) ≫ ((End.of e.hom) ^ m) = 𝟙 X ∧
      ((End.of e.hom) ^ m) ≫ ((End.of e.inv) ^ m) = 𝟙 X := by
  have hmul : Commute (End.of e.hom) (End.of e.inv) := by
    change e.inv ≫ e.hom = e.hom ≫ e.inv
    rw [e.inv_hom_id, e.hom_inv_id]
  constructor
  · change (End.of e.hom) ^ m * (End.of e.inv) ^ m = 1
    rw [← hmul.mul_pow]
    have h : End.of e.hom * End.of e.inv = (1 : End X) := e.inv_hom_id
    rw [h, one_pow]
  · change (End.of e.inv) ^ m * (End.of e.hom) ^ m = 1
    rw [← hmul.symm.mul_pow]
    have h : End.of e.inv * End.of e.hom = (1 : End X) := e.hom_inv_id
    rw [h, one_pow]

/-- Absolute Frobenius and the geometric point power are mutual inverses.
Source: finite-field geometric/arithmetic Frobenius inverse convention
(blueprint: lem-trf-finite-return-scheme-identities).
Proof: the Spec/Gamma adjunction identifies the absolute point power with the m-th power
of the inverse point isomorphism: on k this is the q^m-power automorphism. Powers of an
isomorphism and its inverse cancel in both orders. -/
theorem returnPoint_inverse (T : TraceFormulaCoefficientConventions.{u}) (m : ℕ) :
    T.returnAbsolute
        (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m ≫
      T.returnBasePower m = 𝟙 (Spec (.of T.datum.k)) ∧
    T.returnBasePower m ≫ T.returnAbsolute
        (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m =
      𝟙 (Spec (.of T.datum.k)) := by
  rw [returnAbsolutePoint_eq]
  exact iso_power_inverse (frobeniusPointIso T.datum) m

/-- Scheme Frobenius factors as absolute Frobenius followed by geometric Galois.
Source: `prop-trf-frobenius-factorization`
(blueprint: lem-trf-finite-return-scheme-identities).
Proof: the existing absolute-Frobenius factorization is Phi^m followed by the arithmetic
Galois power. Compose with the geometric power and cancel the inverse powers. -/
theorem returnFactorization (T : TraceFormulaCoefficientConventions.{u})
    (m : ℕ) (hm : 1 ≤ m) :
    T.datum.schemeFrobeniusIterate T.X₀ m =
      T.returnAbsolute (W := T.geometricBaseChange) (T.structureMap ≫
        Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m ≫
        HPow.hPow (α := End T.geometricBaseChange)
          (T.datum.geometricGaloisFrobenius T.X₀) m := by
  have hf := (T.datum.absoluteFrobenius_factorization T.X₀ m hm).1
  change T.returnAbsolute (T.structureMap ≫
    Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m =
      T.datum.schemeFrobeniusIterate T.X₀ m ≫
        (End.of (T.datum.geometricFrobenius T.X₀).inv) ^ m at hf
  change T.datum.schemeFrobeniusIterate T.X₀ m = _ ≫
    (End.of (T.datum.geometricFrobenius T.X₀).hom) ^ m
  rw [hf, Category.assoc, (iso_power_inverse (T.datum.geometricFrobenius T.X₀) m).1,
    Category.comp_id]

private theorem inverse_restrictions_apply
    {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat}
    (M : PresheafOfModules R) {U V : C} (f : U ⟶ V) (g : V ⟶ U)
    (h : g ≫ f = 𝟙 V) (x : M.obj (op V)) :
    M.map g.op (M.map f.op x) = x := by
  rw [← M.map_comp_apply]
  exact (M.congr_map_apply (congrArg Quiver.Hom.op h) x).trans (by
    rw [op_id, M.map_id]
    rfl)

/-- The two return restrictions are inverse on arbitrary module-sheaf sections.
Source: functoriality of module presheaf restriction
(blueprint: lem-trf-finite-return-scheme-identities).
Proof: the faithful forgetful functor to schemes over s identifies the composites of the
site arrows with r h and h r, both identities. Apply PresheafOfModules.map_comp_apply
and its identity-map law. These are equalities of functions on sections, so changing
scalar restrictions in the semilinear maps introduces no additional comparison. -/
theorem returnRestriction_inverse_sections
    (T : TraceFormulaCoefficientConventions.{u}) (m : ℕ)
    (w : T.returnAbsolute
      (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m ≫
      T.returnBasePower m = 𝟙 (Spec (.of T.datum.k)))
    (w' : T.returnBasePower m ≫ T.returnAbsolute
      (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) m =
      𝟙 (Spec (.of T.datum.k)))
    (N : proEtaleRingModules (Spec (.of T.datum.k))
      (proEtaleConstantRing (Spec (.of T.datum.k)) T.coefficientRing)) :
    (∀ x, N.val.map (T.returnRestrictionInverse m w).op
      (N.val.map (T.returnRestriction m).op x) = x) ∧
    (∀ x, N.val.map (T.returnRestriction m).op
      (N.val.map (T.returnRestrictionInverse m w).op x) = x) := by
  obtain ⟨h₁, h₂⟩ := returnRestriction_comp T m w w'
  exact ⟨inverse_restrictions_apply N.val (T.returnRestriction m)
      (T.returnRestrictionInverse m w) h₁,
    inverse_restrictions_apply N.val (T.returnRestrictionInverse m w)
      (T.returnRestriction m) h₂⟩

private theorem inverse_model_unit
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (V : Y.ProEt)
    (x : M.val.obj (op V)) :
    ((openSquarePullbackModel A f).inv.app M).val.app
      (op ((proEtaleBaseChange f).obj V))
      (((sfIntrinsicConstantModuleAdjunction f A).unit.app M).val.app (op V) x) =
        ((proEtaleConstantRingAdjunction A f).unit.app M).val.app (op V) x := by
  have hu := (openSquarePullbackModel_existsUnique A f).exists.choose_spec M V x
  have hi := congrArg (fun a ↦ a.val.app (op ((proEtaleBaseChange f).obj V))
      (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (op V) x))
    ((openSquarePullbackModel A f).hom_inv_id_app M)
  change ((openSquarePullbackModel A f).inv.app M).val.app _
    (((openSquarePullbackModel A f).hom.app M).val.app _ _) = _ at hi
  exact (congrArg (((openSquarePullbackModel A f).inv.app M).val.app _) hu).symm.trans hi

/-- The finite inverse-image comparison, in the actual intrinsic coordinates,
is precisely the distinguished graph-unit insertion on every degree and section.
Source: current blueprint, lem-trf-absolute-frobenius-site.proof.md, point-transport
specialization; Stacks Tags 03D6 and 00YV
(blueprint: lem-trf-finite-return-scheme-identities).
Proof: the finite comparison is specified by restriction of its adjunction-unit section
along the distinguished comma arrow. The intrinsic coordinate comparison is the unique
unit-preserving comparison of the two left adjoints. Its naturality moves it past the
restriction, and its unit equation identifies the remaining section with the intrinsic
unit section. This holds for every site object and every term of every complex. -/
theorem returnIntrinsicInverseImage_insertion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)
    [Finite (Padic.coefficientExtensionRing l E (n + 1))]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ)
    (i : ℤ) (U : X.ProEt)
    (x : (K.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((inverseImageFiniteIntrinsicPullbackComparison g
      (Padic.coefficientExtensionRing l E (n + 1))).hom.app (K.X i)).val.app (op U)
      (((inverseImageFiniteComparisonComplex l E g n K).f i).val.app (op U) x) =
    ((sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) g).obj
      (K.X i)).val.map (proEtaleIsoCommaArrow g U).op
      (((sfIntrinsicConstantModuleAdjunction g
        (Padic.coefficientExtensionRing l E (n + 1))).unit.app (K.X i)).val.app
        (op ((proEtaleIsoPostcompose g).obj U)) x) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let M := K.X i
  let β := (inverseImageFiniteIntrinsicPullbackComparison g A).hom.app M
  let V := (proEtaleIsoPostcompose g).obj U
  let a := coefficientProEtaleModuleAdjunction.{u, u} g
    (CommRingCat.of (ULift.{u + 1, u} A))
  let b := sfIntrinsicConstantModuleAdjunction g A
  have hc := (inverseImageFiniteComparison_existsUnique l E g n K).exists.choose_spec i U x
  have hu := congrArg (fun z ↦ z.val.app (op V) x)
    (a.unit_leftAdjointUniq_hom_app b M)
  change β.val.app (op ((proEtaleBaseChange g).obj V))
    ((a.unit.app M).val.app (op V) x) =
      (b.unit.app M).val.app (op V) x at hu
  exact (congrArg (β.val.app (op U)) hc).trans
    ((PresheafOfModules.naturality_apply β.val (proEtaleIsoCommaArrow g U).op
      ((a.unit.app M).val.app (op V) x)).trans
      (congrArg (((sfIntrinsicPullback A g).obj M).val.map
        (proEtaleIsoCommaArrow g U).op) hu))

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

/-- Arrows into a pro-etale object with monomorphic structure map are unique.
Source: Mathlib over-category commutativity and cancellation of monomorphisms;
current blueprint point-site arrow identifications
(blueprint: lem-trf-finite-return-scheme-identities).
Proof: forget to the category of schemes over the base. Both underlying arrows,
composed with the target structure map, equal the source structure map. Cancel that
monomorphism, use over-morphism extensionality, then faithfulness of the forgetful functor.
In particular this applies to every point-site object with isomorphic structure map. -/
theorem returnSiteArrow_unique {S : Scheme.{u}} {U V : S.ProEt} [Mono V.hom]
    (f g : U ⟶ V) : f = g := by
  apply (ProEt.forget S).map_injective
  apply Over.OverMorphism.ext
  apply (cancel_mono V.hom).1
  exact (Over.w ((ProEt.forget S).map f)).trans
    (Over.w ((ProEt.forget S).map g)).symm

end WeilConjectures.TraceFormulaCoefficientConventions
