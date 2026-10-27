/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q131
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.RationalModuleRealizationFunctor
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientGeneralPullbackIso
import all Sheaf.Paper.PbcScalarRestriction
import all Sheaf.Paper.PbcActualStrictPullback
import all Sheaf.Paper.CompletedTowerPullback
import all Sheaf.Paper.PbcScalarTriangulation
import all Sheaf.AlgebraicGeometry.ContinuousCoefficientBasic
import Sheaf.Paper.PbcRationalTransport
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Completed pullback and descent on raw scalar fractions

Source: Bhatt--Scholze, Remark 6.8.15 and Proposition 6.8.14(2), with the explicit
scalar and fraction calculations of the DAG
(blueprint: lem-per-completed-pullback-fraction-descent).

The valuation ring uses the existing size lift `PbcIntegralRing`. Rational module
sheaves are presented by the dependency's normalized continuous-coefficient model
of sheaf localization. No faithfulness hypothesis on realization is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
namespace CompletedPullbackFractions

open scoped TensorProduct

section FractionAlgebra
universe r v
variable {A : Type r} [CommRing A] (p : A)
  {M : Type v} [AddCommGroup M] [Module A M]

private theorem tensor_fraction_mk (f : M) (n : ℕ) :
    (IsLocalization.Away.invSelf p : Localization.Away p) ^ n •
        ((1 : Localization.Away p) ⊗ₜ[A] f) =
      IsLocalizedModule.mk' (TensorProduct.mk A (Localization.Away p) M 1) f
        (⟨p ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers p) := by
  symm
  apply IsLocalizedModule.mk'_eq_iff.mpr
  change (1 : Localization.Away p) ⊗ₜ[A] f =
    (p ^ n) • ((IsLocalization.Away.invSelf p : Localization.Away p) ^ n •
      ((1 : Localization.Away p) ⊗ₜ[A] f))
  rw [← IsScalarTower.algebraMap_smul (Localization.Away p) (p ^ n), smul_smul,
    map_pow, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, one_smul]

private theorem tensor_fraction_eq (f h : M) (n m : ℕ) :
    (IsLocalization.Away.invSelf p : Localization.Away p) ^ n •
        ((1 : Localization.Away p) ⊗ₜ[A] f) =
        (IsLocalization.Away.invSelf p : Localization.Away p) ^ m •
          ((1 : Localization.Away p) ⊗ₜ[A] h) ↔
      ∃ r : ℕ, p ^ r • (p ^ m • f - p ^ n • h) = 0 := by
  rw [tensor_fraction_mk, tensor_fraction_mk, IsLocalizedModule.mk'_eq_mk'_iff]
  simp only [Submonoid.smul_def, Submonoid.mem_powers_iff, Subtype.exists,
    exists_prop]
  constructor
  · rintro ⟨a, ⟨r, rfl⟩, hr⟩
    exact ⟨r, by rw [smul_sub, sub_eq_zero]; exact hr.symm⟩
  · rintro ⟨r, hr⟩
    refine ⟨p ^ r, ⟨r, rfl⟩, ?_⟩
    exact (sub_eq_zero.mp (by simpa only [smul_sub] using hr)).symm

private theorem tensor_fraction_add (f h : M) (n m : ℕ) :
    (IsLocalization.Away.invSelf p : Localization.Away p) ^ n •
        ((1 : Localization.Away p) ⊗ₜ[A] f) +
        (IsLocalization.Away.invSelf p : Localization.Away p) ^ m •
          ((1 : Localization.Away p) ⊗ₜ[A] h) =
      (IsLocalization.Away.invSelf p : Localization.Away p) ^ (n + m) •
        ((1 : Localization.Away p) ⊗ₜ[A] (p ^ m • f + p ^ n • h)) := by
  rw [tensor_fraction_mk, tensor_fraction_mk, tensor_fraction_mk,
    IsLocalizedModule.mk'_add_mk']
  simp only [Submonoid.smul_def, pow_add]
  rfl

end FractionAlgebra

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing full category, including compatible etale-origin witnesses.
Source: Bhatt--Scholze, Section 6.8
(blueprint: lem-per-completed-pullback-fraction-descent). -/
abbrev Integral (X : Scheme.{u}) :=
  PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)

/-- The existing raw scalar localization, without idempotent completion.
Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-completed-pullback-fraction-descent). -/
abbrev Rational (X : Scheme.{u}) :=
  PbcRationalCategory X (pbcIntegralDatum l E) (pbcUniformizer l E)

/-- The prescribed integral-to-raw functor.
Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-completed-pullback-fraction-descent). -/
abbrev Q (X : Scheme.{u}) : Integral l E X ⥤ Rational l E X :=
  pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)

/-- A fraction in the existing tensor Hom module; no torsion is cancelled.
Source: Bhatt--Scholze, Section 6.8 rationalization
(blueprint: lem-per-completed-pullback-fraction-descent). -/
def fraction {X : Scheme.{u}} {K L : Integral l E X} (f : K ⟶ L) (n : ℕ) :
    (Q l E X).obj K ⟶ (Q l E X).obj L :=
  (IsLocalization.Away.invSelf (S := Localization.Away (pbcUniformizer l E))
    (pbcUniformizer l E)) ^ n • (Q l E X).map f

/-- The ordinary rational derived pullback in the specified localization model.
The coefficient map is continuous precomposition, which is the normalized
localization of the integral coefficient map, not an arbitrary ring morphism.
Source: Bhatt--Scholze, Remark 6.8.15
(blueprint: lem-per-completed-pullback-fraction-descent). -/
abbrev rationalPull {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  proEtaleRingDerivedPullback g (rationalCoefficientSheaf l Y E)
    (rationalCoefficientSheaf l X E) (asIso (rationalContinuousPullback l E g))

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  (g : X ⟶ Y)
  (hP : ∀ K : Integral l E Y, PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
    ((completedOrdinaryPullback g (pbcIntegralDatum l E)).obj K.obj))

/-- Expose the coefficient action already supplied by a realization witness.
This merely activates its normalized module action in the derived category.
Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-completed-pullback-fraction-descent). -/
def realizationSmul {T : Scheme.{u}} [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (J : RationalModuleRealization l E T) (a : E)
    {K L : DerivedCategory (pbcModules T (rationalCoefficientSheaf l T E))}
    (f : K ⟶ L) : K ⟶ L := by
  letI := J.moduleLinear
  exact a • f

omit [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))] in
private theorem coefficient_constants :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (pbcCompletedScalar Y (pbcIntegralDatum l E)) ≫
      completedCoefficientMap g (pbcIntegralDatum l E) =
    proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
        (CommRingCat.of (PbcIntegralRing l E)) ≫
      pbcCompletedScalar X (pbcIntegralDatum l E) := by
  let d := pbcIntegralDatum l E
  have hp (W : Scheme.{u}) (n : ℕ) :
      pbcCompletedScalar W d ≫ pbcAdicProjection W d n =
        (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
            (pbcLevelConstantComparison W d n).hom := by
    dsimp only [pbcCompletedScalar, pbcAdicProjection, pbcCompletedComparison]
    rw [Category.assoc]
    erw [HasLimit.isoOfNatIso_hom_π]
    rw [← Category.assoc]
    erw [(adicDatumScalar_exists W
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite }).exists.choose_spec n]
    rfl
  change (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      (pbcCompletedScalar Y d) ≫ completedCoefficientMap g d =
    proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
      (CommRingCat.of (PbcIntegralRing l E)) ≫ pbcCompletedScalar X d
  have hc (n : ℕ) : completedCoefficientMap g d ≫ pbcAdicProjection X d n =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (pbcAdicProjection Y d n) ≫ completedFiniteCoefficientMap g d n := by
    exact limit.lift_π _ (op n)
  symm
  apply limit.hom_ext
  rintro ⟨n⟩
  change _ ≫ pbcAdicProjection X d n = _ ≫ pbcAdicProjection X d n
  rw [Category.assoc, hp]
  rw [Category.assoc, hc]
  simp only [completedFiniteCoefficientMap]
  rw [← Functor.map_comp_assoc, hp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc _ (pbcLevelConstantComparison Y d n).hom
    (pbcLevelConstantComparison Y d n).inv, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact (proEtaleConstantInverseImageMap_naturality g
    (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))).symm =≫ _

omit [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))] in
private theorem strict_unit_app (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K =
      completedPullbackComparison g (pbcIntegralDatum l E) K := by
  simp only [pbcActualStrictCompletedPullUnit, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp, completedPullbackComparison,
    Functor.comp_obj]

private theorem rational_constant (T : Scheme.{u}) (U : T.ProEtᵒᵖ) (a : E) :
    let := coefficientExtensionNormedField l E
    (@id C(U.unop.left, ULift.{u + 1, u} E) ((rationalModuleConstantMap l E T).hom.app U
        ((toSheafify (ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))).app U
            (ULift.up a)))) = ContinuousMap.const U.unop.left
              (ULift.up.{u + 1, u} a) := by
  let := coefficientExtensionNormedField l E
  change ((((sheafificationAdjunction (ProEt.topology T)
    CommRingCat.{u + 1}).homEquiv _ _)
      (rationalModuleConstantMap l E T)).app U) (ULift.up a) = _
  rw [rationalModuleConstantMap, Equiv.apply_symm_apply]
  rfl

private theorem rationalPull_linear
    (JY : RationalModuleRealization l E Y) (JX : RationalModuleRealization l E X) :
    let := JY.moduleLinear
    let := JX.moduleLinear
    (rationalPull l E g).Linear E := by
  let := JY.moduleLinear
  let := JX.moduleLinear
  let := coefficientExtensionNormedField l E
  let RY := rationalCoefficientSheaf l Y E
  let RX := rationalCoefficientSheaf l X E
  let c := asIso (rationalContinuousPullback l E g)
  have hc : proEtaleRingDirectImageMap g RY RX c =
      continuousCoefficientDirectMap (ULift.{u + 1} E) g := by
    change ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _)
      (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _
  have : (proEtaleRingModuleDirectImage g RY RX c).Linear E := by
    constructor
    intro M N f a
    ext U x
    change (a • f).val.app ((proEtaleBaseChange g).op.obj U) x =
      (a • (proEtaleRingModuleDirectImage g RY RX c).map f).val.app U x
    rw [JX.scalar_normalization, JY.scalar_normalization]
    change _ • f.val.app ((proEtaleBaseChange g).op.obj U) x =
      ((proEtaleRingDirectImageMap g RY RX c).hom.app U _) •
        f.val.app ((proEtaleBaseChange g).op.obj U) x
    congr 1
    rw [hc]
    have hx := rational_constant l E X ((proEtaleBaseChange g).op.obj U) a
    have hy := rational_constant l E Y U a
    dsimp only [id] at hx hy
    rw [hx, hy]
    rfl
  have : (proEtaleRingModulePullback g RY RX c).Linear E :=
    (proEtaleRingModuleAdjunction g RY RX c).left_adjoint_linear
  exact inferInstanceAs ((proEtaleRingModulePullback g RY RX c).mapDerivedCategory.Linear E)

private theorem coefficient_inverse :
    pbcRationalCoefficientEquiv l E
      (IsLocalization.Away.invSelf (pbcUniformizer l E)) =
        ((pbcUniformizer l E).down.val)⁻¹ := by
  have h (a : PbcIntegralRing l E) :
      pbcRationalCoefficientEquiv l E (algebraMap _ _ a) = a.down.val := by
    unfold pbcRationalCoefficientEquiv
    rw [RingEquiv.trans_apply]
    erw [IsLocalization.ringEquivOfRingEquiv_eq]
    exact (Padic.coefficientExtension_localization_uniformizer l E).2.choose.commutes a.down
  apply eq_inv_of_mul_eq_one_left
  rw [mul_comm, ← h, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]

attribute [local irreducible] pbcRationalCoefficientEquiv

private theorem coefficient_inverse_power (n : ℕ) :
    (IsLocalization.Away.invSelf (pbcUniformizer l E) :
        Localization.Away (pbcUniformizer l E)) ^ n =
      (pbcRationalCoefficientEquiv l E).symm (((pbcUniformizer l E).down.val ^ n)⁻¹) := by
  apply (pbcRationalCoefficientEquiv l E).injective
  rw [RingEquiv.apply_symm_apply, map_pow, coefficient_inverse, inv_pow]

/-- The normalized outputs and all clauses of completed-pullback fraction descent.
The functor fields are constrained on every object and every fraction. The last
fields extend arbitrary integral natural transformations by the same components.
Source: Bhatt--Scholze, Remark 6.8.15 and Section 6.8 rationalization
(blueprint: lem-per-completed-pullback-fraction-descent). -/
structure Descent
    (hγ : ∀ K : Integral l E Y,
      IsIso (completedPullbackComparison g (pbcIntegralDatum l E) K.obj))
    (JY : RationalModuleRealization l E Y)
    (JX : RationalModuleRealization l E X) where
  /-- The projection-defined coefficient map fixes the entire constant ring. -/
  coefficient_constants :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (pbcCompletedScalar Y (pbcIntegralDatum l E)) ≫
      completedCoefficientMap g (pbcIntegralDatum l E) =
    proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
        (CommRingCat.of (PbcIntegralRing l E)) ≫
      pbcCompletedScalar X (pbcIntegralDatum l E)
  /-- The ordinary restricted pullback preserves addition. -/
  ordinary_additive : (pbcConditionalIntegral (pbcIntegralDatum l E)
    (completedOrdinaryPullback g (pbcIntegralDatum l E)) hP).Additive
  /-- The ordinary restricted pullback preserves every constant A-scalar. -/
  ordinary_linear : (pbcConditionalIntegral (pbcIntegralDatum l E)
    (completedOrdinaryPullback g (pbcIntegralDatum l E)) hP).Linear (PbcIntegralRing l E)
  /-- The given invertible comparison transports full-subcategory membership. -/
  completed_mem : ∀ K : Integral l E Y,
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K.obj)
  /-- The completed restricted pullback preserves addition. -/
  completed_additive : (pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g) completed_mem).Additive
  /-- The completed restricted pullback preserves every constant A-scalar. -/
  completed_linear : (pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g) completed_mem).Linear
      (PbcIntegralRing l E)
  /-- Conjugation uses the specified comparison, with no substituted completion unit. -/
  conjugation : ∀ (K L : Integral l E Y) (f : K ⟶ L),
    (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).map f.hom =
      @CategoryTheory.inv _ _ _ _
          (completedPullbackComparison g (pbcIntegralDatum l E) K.obj) (hγ K) ≫
        (completedOrdinaryPullback g (pbcIntegralDatum l E)).map f.hom ≫
          completedPullbackComparison g (pbcIntegralDatum l E) L.obj
  /-- The raw rationalized completed pullback. -/
  bar : Rational l E Y ⥤ Rational l E X
  /-- Fraction addition is preserved. -/
  bar_additive : bar.Additive
  /-- Its object is exactly the rationalization of completed pullback. -/
  bar_objects : ∀ K : Integral l E Y,
    bar.obj ((Q l E Y).obj K) = (Q l E X).obj
      ((pbcConditionalIntegral (pbcIntegralDatum l E)
        (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g) completed_mem).obj K)
  /-- Every denominator is retained, with only the required object transports. -/
  bar_fractions : ∀ (K L : Integral l E Y) (f : K ⟶ L) (n : ℕ),
    bar.map (fraction l E f n) = eqToHom (bar_objects K) ≫
      fraction l E ((pbcConditionalIntegral (pbcIntegralDatum l E)
        (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g) completed_mem).map f) n ≫
        eqToHom (bar_objects L).symm
  /-- The torsion-sensitive equality relation on the original fractions. -/
  fraction_eq : ∀ (K L : Integral l E Y) (f h : K ⟶ L) (n m : ℕ),
    fraction l E f n = fraction l E h m ↔
      ∃ r : ℕ, (pbcUniformizer l E) ^ r •
        ((pbcUniformizer l E) ^ m • f - (pbcUniformizer l E) ^ n • h) = 0
  /-- The very same annihilating power works after completed pullback. -/
  annihilator : ∀ (K L : Integral l E Y) (f h : K ⟶ L) (n m r : ℕ),
    (pbcUniformizer l E) ^ r •
        ((pbcUniformizer l E) ^ m • f - (pbcUniformizer l E) ^ n • h) = 0 →
    (pbcUniformizer l E) ^ r •
      ((pbcUniformizer l E) ^ m •
        (pbcConditionalIntegral (pbcIntegralDatum l E)
          (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g) completed_mem).map f -
       (pbcUniformizer l E) ^ n •
        (pbcConditionalIntegral (pbcIntegralDatum l E)
          (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g) completed_mem).map h) = 0
  /-- Addition is the common-denominator operation. -/
  fraction_add : ∀ (K L : Integral l E Y) (f h : K ⟶ L) (n m : ℕ),
    fraction l E f n + fraction l E h m =
      fraction l E ((pbcUniformizer l E) ^ m • f + (pbcUniformizer l E) ^ n • h) (n + m)
  /-- Composition multiplies denominators. -/
  fraction_comp : ∀ (K L M : Integral l E Y) (f : K ⟶ L) (h : L ⟶ M) (n m : ℕ),
    fraction l E f n ≫ fraction l E h m = fraction l E (f ≫ h) (m + n)
  /-- H extends as the literal composite J_X' after bar, with the fraction formula. -/
  H_fractions : ∀ (K L : Integral l E Y) (f : K ⟶ L) (n : ℕ),
    (bar ⋙ JX.J).map (fraction l E f n) =
      realizationSmul l E JX (((pbcUniformizer l E).down.val ^ n)⁻¹)
        ((bar ⋙ JX.J).map ((Q l E Y).map f))
  /-- G extends as ordinary rational pullback after J_Y, with the fraction formula. -/
  G_fractions : ∀ (K L : Integral l E Y) (f : K ⟶ L) (n : ℕ),
    (JY.J ⋙ rationalPull l E g).map (fraction l E f n) =
      realizationSmul l E JX (((pbcUniformizer l E).down.val ^ n)⁻¹)
        ((JY.J ⋙ rationalPull l E g).map ((Q l E Y).map f))
  /-- Every integral comparison has a unique extension with identical components. -/
  comparisons : ∀ β :
      (pbcConditionalIntegral (pbcIntegralDatum l E)
        (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g) completed_mem ⋙
          Q l E X) ⋙ JX.J ⟶ Q l E Y ⋙ (JY.J ⋙ rationalPull l E g),
    ∃! b : bar ⋙ JX.J ⟶ JY.J ⋙ rationalPull l E g,
      ∀ K : Integral l E Y, b.app ((Q l E Y).obj K) =
        JX.J.map (eqToHom (bar_objects K)) ≫ β.app K
  /-- Componentwise invertibility makes every such extension a natural isomorphism. -/
  comparisons_iso : ∀ (β :
      (pbcConditionalIntegral (pbcIntegralDatum l E)
        (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g) completed_mem ⋙
          Q l E X) ⋙ JX.J ⟶ Q l E Y ⋙ (JY.J ⋙ rationalPull l E g))
      (b : bar ⋙ JX.J ⟶ JY.J ⋙ rationalPull l E g),
    (∀ K : Integral l E Y, b.app ((Q l E Y).obj K) =
        JX.J.map (eqToHom (bar_objects K)) ≫ β.app K) →
    (∀ K : Integral l E Y, IsIso (β.app K)) → IsIso b

/-- Completed pullback is linear and descends, together with all integral natural
comparisons, to the actual raw rationalization.
Source: Bhatt--Scholze, Remark 6.8.15 and Proposition 6.8.14(2)
(blueprint: lem-per-completed-pullback-fraction-descent).

Proof, following the six steps of the node:
1. Project the coefficient map to each finite quotient. The constant residue of every
A-scalar is preserved by the normalized constant inverse-image map. Joint monicity of
limit projections gives coefficient_constants; preservation of this limit by inverse
image, or invertibility of the coefficient map, is not needed.
2. Apply lem-weil-pbc-ringed-topoi-derived-pullback. Use a flat-term K-flat resolution
from lem-pc-kflat-resolution to compute multiplication by a scalar on a representative.
Tensor balancing and Step 1 give multiplication by the same scalar after pullback.
Every arrow af is the composite of f with a scalar identity, giving ordinary linearity.
3. Naturality of the specified gamma gives conjugation. Its assumed invertibility
transports completed constructibility, including the etale-origin witnesses, and
transports additivity and A-linearity to the completed restriction.
4. Identify each raw Hom with module localization using
lem-weil-l-adic-integers-localization-uniformizer and
lem-weil-pbc-localization-module-tensor. Equality of fractions means some further power
annihilates the cross-multiplied difference, even with torsion. Linearity preserves the
same power. The displayed sum and composition laws construct bar on all fractions.
5. Use lem-weil-pbc-localization-inverse-image-coherence to localize the coefficient
map. In the specified continuous model this is rationalContinuousPullback. The same
scalar-identity computation gives E-linearity of rational derived pullback. Composing
with the given realizations gives H_fractions and G_fractions.
6. Keep the components of any integral beta. Substituting the fraction formulas into
naturality gives varpi^(-n) times its integral naturality equation. Thus the components
are natural for every raw fraction. Every raw object is an integral object, proving
uniqueness. If the components are invertible, their inverses are natural by multiplying
the naturality equation on both sides. No faithfulness of either realization is used. -/
theorem completedPullbackFractionDescent
    (hγ : ∀ K : Integral l E Y,
      IsIso (completedPullbackComparison g (pbcIntegralDatum l E) K.obj))
    (JY : RationalModuleRealization l E Y) (JX : RationalModuleRealization l E X) :
    Nonempty (Descent l E g hP hγ JY JX) := by
  classical
  let := JY.moduleLinear
  let := JX.moduleLinear
  let := JY.additive
  let := JY.linear
  let := JX.additive
  let := JX.linear
  let : Module (PbcIntegralRing l E) (Localization.Away (pbcUniformizer l E)) :=
    OreLocalization.instModuleOfIsScalarTower
  have : (rationalPull l E g).Linear E := rationalPull_linear l E g JY JX
  have : (completedOrdinaryPullback g (pbcIntegralDatum l E)).Additive :=
    (pbcActualDerivedAdjunction g (pbcIntegralDatum l E)).left_adjoint_additive
  have : (completedOrdinaryPullback g (pbcIntegralDatum l E)).Linear
      (PbcIntegralRing l E) :=
    (pbcActualDerivedAdjunction g (pbcIntegralDatum l E)).left_adjoint_linear
  let O := pbcConditionalIntegral (pbcIntegralDatum l E)
    (completedOrdinaryPullback g (pbcIntegralDatum l E)) hP
  have := (pbcIntegralUniformComplete_isTriangulated l E X
    (Fact.out : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (Fact.out : ∀ x : X, IsUnit (l : X.presheaf.stalk x))).1
  have hmem (K : Integral l E Y) :
      PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
        ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K.obj) := by
    let := hγ K
    exact ObjectProperty.prop_of_iso _
      (asIso (completedPullbackComparison g (pbcIntegralDatum l E) K.obj)) (hP K)
  let C := pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g) hmem
  let e : O ≅ C := NatIso.ofComponents (fun K ↦ by
    let := hγ K
    exact ObjectProperty.isoMk _
      (asIso (completedPullbackComparison g (pbcIntegralDatum l E) K.obj))) (by
        intro K L f
        apply ObjectProperty.hom_ext
        change (completedOrdinaryPullback g (pbcIntegralDatum l E)).map f.hom ≫
            completedPullbackComparison g (pbcIntegralDatum l E) L.obj =
          completedPullbackComparison g (pbcIntegralDatum l E) K.obj ≫
            (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).map f.hom
        simpa only [strict_unit_app] using
          (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).naturality f.hom)
  have : C.Additive := Functor.additive_of_iso e
  have : C.Linear (PbcIntegralRing l E) := Functor.linear_of_iso (PbcIntegralRing l E) e
  let B := ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E) C
  have : B.Linear E := ⟨fun f a ↦
    B.map_smul ((pbcRationalCoefficientEquiv l E).symm a) f⟩
  have hfrac (T : Scheme.{u}) [IsNoetherian T]
      [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
      [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
      {K L : Integral l E T} (f : K ⟶ L) (n : ℕ) :
      fraction l E f n = ((pbcUniformizer l E).down.val ^ n)⁻¹ • (Q l E T).map f := by
    change (IsLocalization.Away.invSelf (pbcUniformizer l E) :
        Localization.Away (pbcUniformizer l E)) ^ n • (Q l E T).map f =
      ((pbcRationalCoefficientEquiv l E).symm
        (((pbcUniformizer l E).down.val ^ n)⁻¹)) • (Q l E T).map f
    exact congrArg (fun a : Localization.Away (pbcUniformizer l E) ↦
      a • (Q l E T).map f) (coefficient_inverse_power l E n)
  refine ⟨{
    coefficient_constants := coefficient_constants l E g
    ordinary_additive := inferInstance
    ordinary_linear := inferInstance
    completed_mem := hmem
    completed_additive := inferInstanceAs C.Additive
    completed_linear := inferInstanceAs (C.Linear (PbcIntegralRing l E))
    conjugation := ?_
    bar := B
    bar_additive := inferInstance
    bar_objects := fun _ ↦ rfl
    bar_fractions := ?_
    fraction_eq := ?_
    annihilator := ?_
    fraction_add := ?_
    fraction_comp := ?_
    H_fractions := ?_
    G_fractions := ?_
    comparisons := ?_
    comparisons_iso := ?_ }⟩
  · intro K L f
    let := hγ K
    apply (cancel_epi (completedPullbackComparison g (pbcIntegralDatum l E) K.obj)).mp
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    simpa only [strict_unit_app] using
      ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).naturality f.hom).symm
  · intro K L f n
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (ScalarLocalization.transportHom (PbcIntegralRing l E)
      (pbcUniformizer l E) C K L) (_ • _) = _
    rw [map_smul]
    simp only [fraction, Q, pbcRationalization, ScalarLocalization.localization,
      ScalarLocalization.transportHom, LinearMap.baseChange_tmul]
    rfl
  · intro K L f h n m
    exact tensor_fraction_eq (pbcUniformizer l E) f h n m
  · intro K L f h n m r hr
    simpa only [Functor.map_smul, Functor.map_sub, Functor.map_zero] using congrArg C.map hr
  · intro K L f h n m
    exact tensor_fraction_add (pbcUniformizer l E) f h n m
  · intro K L M f h n m
    simp only [fraction, Linear.smul_comp, Linear.comp_smul, smul_smul,
      ← Functor.map_comp, ← pow_add]
  · intro K L f n
    change (B ⋙ JX.J).map _ = _ • _
    rw [hfrac, Functor.map_smul]
  · intro K L f n
    change (JY.J ⋙ rationalPull l E g).map _ = _ • _
    rw [hfrac, Functor.map_smul]
  · intro β
    let H := B ⋙ JX.J
    let G := JY.J ⋙ rationalPull l E g
    have hm {K L : Integral l E Y} (f : K ⟶ L) :
        H.map ((Q l E Y).map f) = ((C ⋙ Q l E X) ⋙ JX.J).map f := by
      change JX.J.map ((ScalarLocalization.transportHom (PbcIntegralRing l E)
        (pbcUniformizer l E) C K L) (1 ⊗ₜ f)) = JX.J.map (1 ⊗ₜ C.map f)
      rw [ScalarLocalization.transportHom, LinearMap.baseChange_tmul]
      rfl
    let β' : Q l E Y ⋙ H ⟶ Q l E Y ⋙ G :=
      { app := fun K ↦ β.app K
        naturality := fun K L f ↦ by
          change H.map ((Q l E Y).map f) ≫ β.app L =
            β.app K ≫ (rationalPull l E g).map (JY.J.map ((Q l E Y).map f))
          rw [hm]
          exact β.naturality f }
    let b : H ⟶ G :=
      { app := fun K ↦ β.app K.obj
        naturality := fun K L f ↦ by
          induction f using TensorProduct.induction_on with
          | zero =>
            change H.map (0 : K ⟶ L) ≫ _ = _
            simp only [Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
          | tmul a f =>
            have he : (a ⊗ₜ[PbcIntegralRing l E] f : K ⟶ L) =
                pbcRationalCoefficientEquiv l E a • (Q l E Y).map f := by
              change _ = (pbcRationalCoefficientEquiv l E).symm
                (pbcRationalCoefficientEquiv l E a) • (1 ⊗ₜ f)
              rw [RingEquiv.symm_apply_apply, TensorProduct.smul_tmul',
                smul_eq_mul, mul_one]
            change H.map (a ⊗ₜ[PbcIntegralRing l E] f : K ⟶ L) ≫ _ = _
            rw [he, Functor.map_smul, Functor.map_smul, Linear.smul_comp, Linear.comp_smul]
            exact congrArg (fun z ↦ pbcRationalCoefficientEquiv l E a • z)
              (β'.naturality f)
          | add f h hf hh =>
            rw [H.map_add, G.map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hh] }
    refine ⟨b, ?_, ?_⟩
    · intro K
      change β.app K = JX.J.map (𝟙 _) ≫ β.app K
      rw [JX.J.map_id, Category.id_comp]
    · intro b' hb'
      ext K
      have h := hb' K.obj
      change b'.app K = JX.J.map (𝟙 _) ≫ β.app K.obj at h
      rw [JX.J.map_id, Category.id_comp] at h
      exact h
  · intro β b hb hi
    have hb' (K : Rational l E Y) : IsIso (b.app K) := by
      have := hi K.obj
      change IsIso (b.app ((Q l E Y).obj K.obj))
      rw [hb K.obj]
      infer_instance
    exact NatIso.isIso_of_isIso_app b

end CompletedPullbackFractions
end AlgebraicGeometry.Scheme
