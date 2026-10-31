/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityBaseChange
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityDirectSum
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityFiniteReduction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Normalized.NormalizedVectorPurityBaseChange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Normalized.NormalizedVectorPurityDirectSum
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Normalized.NormalizedVectorPurityScalarReduction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Normalized.NormalizedVectorPurityBundle

/-! # Vector-bundle purity

Source: main-20261015 sec-smooth-purity/sk-prop-an, integration and Steps 4--6
(blueprint: cor-pur-vector-bundle-purity).

## Main definitions

This module gives the canonical comparisons and their displayed source equation.
Every map is constructed before the compatibility proposition is stated.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The finite purity convention, realized on the ordinary derived category.
All geometric and characteristic witnesses follow from the fixed setting.
Source: purity conventions and vector-bundle purity
(blueprint: cor-pur-vector-bundle-purity). -/
def VectorBundlePurityConclusion (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) (hB : B ⟶ Spec (CommRingCat.of P.field.k))
    [LocallyOfFiniteType hB] [QuasiCompact hB]
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d] : Prop :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  letI : IsNoetherian B := isNoetherian_of_locallyOfFiniteType hB
  letI : IsAffineHom (VectorBundleZeroSection.π B d F) :=
    (Etale.vectorIntegration_geometry B d F).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π B d F) :=
    (Etale.vectorIntegration_geometry B d F).2.1
  ∃ hN : IsUnit (ringChar P.Coefficient : Γ(B, ⊤)),
    VectorPurityFunctorConclusion P.Coefficient (VectorBundleZeroSection.π B d F)
      (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) B)
      (P.vectorPurityEtaleCoefficient B d F) (P.vectorPurityTrace B d F hN) ∧
    ∃ γ : VectorPurityGamma P.Coefficient (ringChar P.Coefficient)
      ((ringChar.spec P.Coefficient _).mpr dvd_rfl) B d F,
    VectorPurityGammaNormalized P.Coefficient (ringChar P.Coefficient)
      (Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite P.Coefficient))
      ((ringChar.spec P.Coefficient _).mpr dvd_rfl) B hN d F γ ∧
    (∀ K : (Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} P.Coefficient) B).FullSubcategory, IsIso (γ.app K.obj)) ∧
    PurityBaseChangeEquation P.Coefficient (ringChar P.Coefficient)
      (Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite P.Coefficient))
      ((ringChar.spec P.Coefficient _).mpr dvd_rfl) B hN d F γ ∧
    PurityDirectSumEquation P.Coefficient (ringChar P.Coefficient)
      (Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite P.Coefficient))
      ((ringChar.spec P.Coefficient _).mpr dvd_rfl) B hN d F γ ∧
    PurityFiniteReductionEquation P (ringChar P.Coefficient)
      (Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite P.Coefficient))
      ((ringChar.spec P.Coefficient _).mpr dvd_rfl) B hN d F γ


set_option backward.isDefEq.respectTransparency.types false
attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize
attribute [local irreducible] AlgebraicGeometry.Etale.derivedTensorSymmetry

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
set_option backward.isDefEq.respectTransparency true

private theorem coefficientChar_isUnit (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) (hB : B ⟶ Spec (CommRingCat.of P.field.k)) :
    IsUnit (ringChar P.Coefficient : Γ(B, ⊤)) := by
  classical
  let : Fintype P.field.k₀ := Fintype.ofFinite _
  let : Fact P.field.p.Prime := ⟨P.field.prime⟩
  have : CharP P.field.k₀ P.field.p :=
    charP_of_card_eq_prime_pow (by
      simpa only [Nat.card_eq_fintype_card] using
        P.field.card_base.trans P.field.cardinality_eq)
  have : CharP P.field.k P.field.p :=
    charP_of_injective_algebraMap' P.field.k₀ P.field.p
  have hl : IsUnit (P.coefficients.l : Γ(B, ⊤)) := by
    have hk : IsUnit (P.coefficients.l : P.field.k) := isUnit_iff_ne_zero.mpr
      (CharP.cast_ne_zero_of_ne_of_prime P.field.k (Fact.out : P.coefficients.l.Prime)
        P.coefficients.different.symm)
    let v := (Scheme.ΓSpecIso (.of P.field.k)).inv.hom
    have hv := (hk.map v).map hB.appTop.hom
    simpa only [map_natCast] using hv
  have ha : ((P.coefficients.l ^ P.level : ℕ) : P.Coefficient) = 0 := by
    let O := Padic.coefficientExtensionIntegers P.coefficients.l P.extension
    let m := Padic.coefficientExtensionMaximalIdeal P.coefficients.l P.extension
    have hs := (Padic.extension_integers_dvr P.coefficients.l P.extension
      (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension)
      (spectralNorm_extends (K := Padic P.coefficients.l)
        (L := P.extension))).choose_spec.choose_spec
    have hm : (P.coefficients.l : O) ∈ m := by
      apply (hs.2.1 (P.coefficients.l : O)).2
      have he := spectralNorm_extends (K := Padic P.coefficients.l) (L := P.extension)
        (P.coefficients.l : Padic P.coefficients.l)
      change spectralNorm (Padic P.coefficients.l) P.extension (P.coefficients.l : P.extension)
        < 1
      simpa only [map_natCast] using he.trans_lt (Padic.norm_p_lt_one (p := P.coefficients.l))
    have hg : Ideal.span ({Padic.coefficientExtensionUniformizer P.coefficients.l P.extension} :
        Set O) = m := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    apply ULift.down_injective
    change ((P.coefficients.l ^ P.level : ℕ) :
      Padic.coefficientExtensionRing P.coefficients.l P.extension P.level) = 0
    rw [← map_natCast (Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level)),
      Ideal.Quotient.eq_zero_iff_mem]
    change ((P.coefficients.l ^ P.level : ℕ) : O) ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer P.coefficients.l P.extension} : Set O)
        ^ P.level
    rw [hg, Nat.cast_pow]
    exact Ideal.pow_mem_pow hm P.level
  apply isUnit_of_dvd_unit _ (show IsUnit ((P.coefficients.l ^ P.level : ℕ) : Γ(B, ⊤)) by
    simpa only [Nat.cast_pow] using hl.pow P.level)
  obtain ⟨k, hk⟩ := ringChar.dvd ha
  refine ⟨(k : Γ(B, ⊤)), ?_⟩
  simpa only [Nat.cast_mul] using congrArg (fun n : ℕ ↦ (n : Γ(B, ⊤))) hk



/-- Vector-bundle purity with integration-and-adjunction normalization.
Source: main-20261015 sec-smooth-purity/sk-prop-an, vector-bundle proposition
(blueprint: cor-pur-vector-bundle-purity).

Proof: use the affine finite-type bundle geometry to apply global Nagata
compactification. Ordinary exact extension by zero followed by proper derived direct
image defines Rpi_!. Brown representability on the whole Grothendieck derived
category supplies its right adjoint. Use K-flat resolutions to form tensor and the
projection arrow. The glued, Kummer-normalized integration has invertible adjoint
mate on bounded constructible complexes of finite Tor amplitude. Invert this mate.
The adjunction Hom bijection proves uniqueness and naturality, including its unit
component. Base change preserves the chartwise affine-space trace; equality is glued
as a map of degree-zero sheaves, then transposed. The same argument with iterated
coordinate traces gives direct sums. Scalar extension preserves the Kummer class
and trace, so uniqueness of adjoints and their counit equations gives finite
reduction compatibility. The scalar mate is transposed only after the canonical
compact-support comparison
is inverted. Its source comparison is built from the normalized pure-root tensor
map, the K-flat scalar tensorator and geometric pullback comparison. This gives the
same reduction equality at the coefficient-unit object. The coefficient range is
finite A = A_{E,n}, exactly as specified by the final scope paragraph of the current
def-pur-conventions; the derived-complete, rational and common-stage transports are
separate results of the blueprint's transport section. -/
theorem vectorBundlePurity (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) (hB : B ⟶ Spec (CommRingCat.of P.field.k))
    [LocallyOfFiniteType hB] [QuasiCompact hB]
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    VectorBundlePurityConclusion P B hB d F := by
  let : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  let : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  let : IsNoetherian B := isNoetherian_of_locallyOfFiniteType hB
  let := (Etale.vectorIntegration_geometry B d F).1
  let := (Etale.vectorIntegration_geometry B d F).2.1
  let N := ringChar P.Coefficient
  have hN : 0 < N := Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite P.Coefficient)
  have hA : (N : P.Coefficient) = 0 := (ringChar.spec P.Coefficient _).mpr dvd_rfl
  have hunit : IsUnit (ringChar P.Coefficient : Γ(B, ⊤)) :=
    coefficientChar_isUnit P B hB
  obtain ⟨hpur, γ, hn, hi⟩ := vectorBundleNormalized P.Coefficient N hN hA B hunit d F
  dsimp only [VectorBundlePurityConclusion, vectorPurityEtaleCoefficient, vectorPurityTrace]
  refine ⟨hunit, hpur, γ, hn, fun K ↦ hi K.obj, ?_, ?_, ?_⟩
  · exact vectorIntegrationCounit_baseChange P.Coefficient N hN hA B hunit d F γ hn hi
  · exact vectorIntegrationCounit_directSum P.Coefficient N hN hA B hunit d F γ hn
  · intro m hm hmn
    let : Finite (Padic.coefficientExtensionRing P.coefficients.l P.extension m) :=
      Padic.finite_coefficientExtensionRing P.coefficients.l P.extension m hm
    let : Finite (purityReductionRing P m hm) := inferInstanceAs
      (Finite (ULift.{u + 1} (Padic.coefficientExtensionRing P.coefficients.l P.extension m)))
    exact vectorIntegrationCounit_scalarReduction P.Coefficient N hN hA B hunit d F γ hn hi
      (purityReductionRing P m hm) (purityReductionRingMap P m P.level hm P.level_pos hmn)


end WeilConjectures.PurityFiniteSetting
