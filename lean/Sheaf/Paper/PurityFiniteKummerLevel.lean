/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.Paper.PurityFiniteKummerDefinitions
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.IntrinsicCoefficientTwists
public import Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.SixFunctors.IntrinsicDerivedTensor
public import Sheaf.Paper.TateInverseLimitBaseChange
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Sheaf.Paper.PurityKummerNormalizedProjection
import Sheaf.Paper.PurityKummerNormalizedBaseChange
import Sheaf.Paper.PurTwistIntegralBasis
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.FieldTheory.Finite.Basic
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

/-! # Finite Kummer level of the Tate twist

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-purity-conv/lem-pur-finite-kummer-level.md
(blueprint: lem-pur-finite-kummer-level).

The source is the published inverse-limit/scalar-extension Tate line, not the already
finite etale line of the purity conventions. The comparison is fixed on local tensors
by the N-th root projection. The base-change square uses the coordinatewise root map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures.PurityFiniteSetting

private theorem kummer_prime_power (P : PurityFiniteSetting.{u}) :
    0 < P.ramificationIndex ∧
      Associated (P.coefficients.l : Padic.coefficientExtensionIntegers
        P.coefficients.l P.extension)
        (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension ^
          P.ramificationIndex) := by
  let l := P.coefficients.l
  let E := P.extension
  let O := Padic.coefficientExtensionIntegers l E
  let m := Padic.coefficientExtensionMaximalIdeal l E
  let π := Padic.coefficientExtensionUniformizer l E
  let abv := Padic.coefficientExtensionAbsoluteValue l E
  have h := (Padic.extension_integers_dvr l E abv
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : IsLocalRing O := h.2.2.2.1
  have : IsDiscreteValuationRing O := h.2.2.2.2.2.2.2.1
  have hπ : Ideal.span ({π} : Set O) = m :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : IsLocalRing.maximalIdeal O = m :=
    h.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal O)
  have hirr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr (hm.trans hπ.symm)
  have : CharZero E := charZero_of_injective_algebraMap
    (algebraMap ℚ_[l] E).injective
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hsmall : abv (l : E) < 1 := by
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E),
      spectralNorm_extends (K := ℚ_[l]) (L := E)]
    exact Padic.norm_p_lt_one
  have hnonunit : ¬IsUnit (l : O) := by
    intro hu
    exact (ne_of_lt hsmall) ((h.2.2.1 (l : O)).mp hu)
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hirr
  have heq : P.ramificationIndex = e := by
    change (emultiplicity π (l : O)).toNat = e
    rw [emultiplicity_eq_of_associated_right he,
      emultiplicity_pow_self hirr.ne_zero hirr.not_isUnit, ENat.toNat_natCast]
  rw [heq]
  refine ⟨Nat.pos_of_ne_zero ?_, he⟩
  intro he0
  apply hnonunit
  exact he.isUnit_iff.mpr (by simp [he0])

private theorem kummer_positive (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) :
    1 ≤ P.kummerLevel ∧ P.level = P.ramificationIndex * P.kummerLevel := by
  have he := (kummer_prime_power P).1
  have hn : P.level = P.ramificationIndex * P.kummerLevel :=
    (Nat.mul_div_cancel' h).symm
  exact ⟨by have := P.level_pos; nlinarith [hn], hn⟩

private theorem kummer_ideal (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) :
    Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level =
      Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
        P.coefficients.l P.extension)} : Set _) := by
  have hn := (kummer_positive P h).2
  change Ideal.span {Padic.coefficientExtensionUniformizer P.coefficients.l P.extension} ^
    P.level = Ideal.span {((P.coefficients.l ^ P.kummerLevel : ℕ) :
      Padic.coefficientExtensionIntegers P.coefficients.l P.extension)}
  rw [Nat.cast_pow, hn, pow_mul, Ideal.span_singleton_pow,
    Ideal.span_singleton_pow]
  exact Ideal.span_singleton_eq_span_singleton.mpr
    (Associated.pow_pow (n := P.kummerLevel) (kummer_prime_power P).2).symm

private theorem kummer_log_prime (P : PurityFiniteSetting.{u}) :
    -Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
      (P.coefficients.l : P.extension)) / Real.log P.coefficients.l = 1 := by
  have hp : 1 < (P.coefficients.l : ℝ) := by
    exact_mod_cast (Fact.out : P.coefficients.l.Prime).one_lt
  have hl : Real.log (P.coefficients.l : ℝ) ≠ 0 := (Real.log_pos hp).ne'
  have ha : Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
      (P.coefficients.l : P.extension) = (P.coefficients.l : ℝ)⁻¹ := by
    change spectralNorm ℚ_[P.coefficients.l] P.extension (P.coefficients.l : P.extension) = _
    rw [← map_natCast (algebraMap ℚ_[P.coefficients.l] P.extension),
      spectralNorm_extends (K := ℚ_[P.coefficients.l]) (L := P.extension), Padic.norm_p]
  rw [ha, Real.log_inv, neg_neg, div_self hl]

private theorem kummer_log_uniformizer (P : PurityFiniteSetting.{u}) :
    -Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
      (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension).val) /
        Real.log P.coefficients.l = (P.ramificationIndex : ℝ)⁻¹ := by
  let l := P.coefficients.l
  let E := P.extension
  let O := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  let abv := Padic.coefficientExtensionAbsoluteValue l E
  have h := (Padic.extension_integers_dvr l E abv
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hp : 1 < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl : Real.log (l : ℝ) ≠ 0 := (Real.log_pos hp).ne'
  obtain ⟨he, v, hv⟩ := kummer_prime_power P
  have hv1 : abv ((v : O) : E) = 1 := (h.2.2.1 (v : O)).mp v.isUnit
  have hval := congrArg (fun x : O ↦ abv (x : E)) hv
  simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_pow, map_mul,
    map_pow, hv1, mul_one] at hval
  have hlog := congrArg Real.log hval
  rw [Real.log_pow] at hlog
  have hnorm : abv (l : E) = (l : ℝ)⁻¹ := by
    change spectralNorm ℚ_[l] E (l : E) = _
    rw [← map_natCast (algebraMap ℚ_[l] E),
      spectralNorm_extends (K := ℚ_[l]) (L := E), Padic.norm_p]
  rw [hnorm, Real.log_inv] at hlog
  have he' : (P.ramificationIndex : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  change -Real.log (abv (π : E)) / Real.log (l : ℝ) = _
  field_simp
  nlinarith

private theorem kummer_minimal (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (j : ℕ)
    (hj : ((P.coefficients.l ^ j : ℕ) : P.Ring) = 0) : P.kummerLevel ≤ j := by
  let l := P.coefficients.l
  let E := P.extension
  let O := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : IsLocalRing O := hdvr.2.2.2.1
  have : IsDiscreteValuationRing O := hdvr.2.2.2.2.2.2.2.1
  have hπ : Ideal.span ({π} : Set O) = Padic.coefficientExtensionMaximalIdeal l E :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : IsLocalRing.maximalIdeal O = Padic.coefficientExtensionMaximalIdeal l E :=
    hdvr.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal O)
  have hirr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr (hm.trans hπ.symm)
  change ((l ^ j : ℕ) : O ⧸ Padic.coefficientExtensionIdeal l E P.level) = 0 at hj
  rw [← map_natCast (Ideal.Quotient.mk
    (Padic.coefficientExtensionIdeal l E P.level)), Ideal.Quotient.eq_zero_iff_mem] at hj
  change ((l ^ j : ℕ) : O) ∈ Ideal.span {π} ^ P.level at hj
  rw [Nat.cast_pow, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hj
  have hd : π ^ P.level ∣ π ^ (P.ramificationIndex * j) := by
    rw [pow_mul]
    exact (Associated.pow_pow (n := j) (kummer_prime_power P).2).dvd_iff_dvd_right.mp hj
  have he := (kummer_prime_power P).1
  have hn := (kummer_positive P h).2
  have := (pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit).mp hd
  nlinarith

private theorem kummer_quotient (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) :
    ∃ r : P.Ring ≃+* (Padic.coefficientExtensionIntegers P.coefficients.l P.extension ⧸
        Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension)} : Set _)),
      ∀ x : Padic.coefficientExtensionIntegers P.coefficients.l P.extension,
        r (Ideal.Quotient.mk
          (Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level) x) =
        Ideal.Quotient.mk (Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension)} : Set _)) x := by
  exact ⟨Ideal.quotEquivOfEq (kummer_ideal P h), fun _ ↦ rfl⟩

private theorem finite_basis_quotient (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : ℕ) (b : @Module.Basis (Fin d) ℤ_[l]
      (Padic.coefficientExtensionIntegers l E) _ _
      (Module.compHom _ (Scheme.purTwistIntegersMap l E))) (r : ℕ) :
    Nonempty ((Padic.coefficientExtensionIntegers l E ⧸
      Ideal.span {((l : Padic.coefficientExtensionIntegers l E) ^ r)}) ≃+
        (Fin d → ZMod (l ^ r))) := by
  classical
  let O := Padic.coefficientExtensionIntegers l E
  let : Algebra ℤ_[l] O := (Scheme.purTwistIntegersMap l E).toAlgebra
  let I : Ideal ℤ_[l] := Ideal.span {(l : ℤ_[l]) ^ r}
  let J : Ideal O := Ideal.span {(l : O) ^ r}
  let M : Submodule ℤ_[l] O := J.restrictScalars ℤ_[l]
  let B : Submodule ℤ_[l] (Fin d → ℤ_[l]) := Submodule.pi Set.univ fun _ ↦ I
  have hm : M.map b.equivFun.toLinearMap = B := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ∀ i, i ∈ Set.univ → b.equivFun y i ∈ I
      intro i _
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hy
      have hs : ((l : ℤ_[l]) ^ r) • z = (l : O) ^ r * z := by
        rw [Algebra.smul_def, map_pow, map_natCast]
      rw [← hs]
      rw [map_smul]
      exact Ideal.mem_span_singleton.mpr ⟨b.equivFun z i, rfl⟩
    · intro hx
      have hx' : ∀ i, ((l : ℤ_[l]) ^ r) ∣ x i := by
        intro i
        exact Ideal.mem_span_singleton.mp (hx i (Set.mem_univ _))
      choose y hy using hx'
      refine ⟨((l : ℤ_[l]) ^ r) • b.equivFun.symm y, ?_, ?_⟩
      · change ((l : ℤ_[l]) ^ r) • b.equivFun.symm y ∈ J
        apply Ideal.mem_span_singleton.mpr
        refine ⟨b.equivFun.symm y, ?_⟩
        rw [Algebra.smul_def, map_pow, map_natCast]
      · rw [map_smul]
        change ((l : ℤ_[l]) ^ r) • b.equivFun (b.equivFun.symm y) = x
        rw [LinearEquiv.apply_symm_apply]
        exact funext fun i ↦ (hy i).symm
  let e : (O ⧸ M) ≃ₗ[ℤ_[l]] ((Fin d → ℤ_[l]) ⧸ B) :=
    Submodule.Quotient.equiv M B b.equivFun hm
  let e' : (O ⧸ M) ≃ₗ[ℤ_[l]] (Fin d → ℤ_[l] ⧸ I) :=
    e.trans (Submodule.quotientPi fun _ : Fin d ↦ I)
  let q : ℤ_[l] ⧸ I ≃+* ZMod (l ^ r) :=
    (Ideal.quotEquivOfEq (PadicInt.ker_toZModPow r).symm).trans
      ((PadicInt.toZModPow r).quotientKerEquivOfSurjective (ZMod.ringHom_surjective _))
  exact ⟨e'.toAddEquiv.trans (AddEquiv.piCongrRight fun _ ↦ q.toAddEquiv)⟩

private theorem kummer_basis_rank (P : PurityFiniteSetting.{u}) :
    ∃ f d : ℕ,
      Nat.card (Padic.coefficientExtensionResidueField P.coefficients.l P.extension) =
        P.coefficients.l ^ f ∧
      d = P.ramificationIndex * f ∧
      Nonempty (@Module.Basis (Fin d) ℤ_[P.coefficients.l]
        (Padic.coefficientExtensionIntegers P.coefficients.l P.extension) _ _
        (Module.compHom _ (Scheme.purTwistIntegersMap P.coefficients.l P.extension))) := by
  classical
  let l := P.coefficients.l
  let E := P.extension
  let O := Padic.coefficientExtensionIntegers l E
  let m := Padic.coefficientExtensionMaximalIdeal l E
  let π := Padic.coefficientExtensionUniformizer l E
  let abv := Padic.coefficientExtensionAbsoluteValue l E
  have hO := (Padic.extension_integers_dvr l E abv
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : IsLocalRing O := hO.2.2.2.1
  have : IsDiscreteValuationRing O := hO.2.2.2.2.2.2.2.1
  have : m.IsMaximal := hO.2.2.2.2.1
  have : Finite (O ⧸ m) := hO.2.2.2.2.2.2.2.2.2.2.2.1
  let : Fintype (O ⧸ m) := Fintype.ofFinite _
  have hl : (l : O ⧸ m) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk m), Ideal.Quotient.eq_zero_iff_mem]
    apply (hO.2.1 (l : O)).mpr
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E),
      spectralNorm_extends (K := ℚ_[l]) (L := E)]
    exact Padic.norm_p_lt_one
  let : Field (O ⧸ m) := Ideal.Quotient.field m
  have : CharP (O ⧸ m) l := (CharP.charP_iff_prime_eq_zero
    (Fact.out : l.Prime)).mpr hl
  obtain ⟨f, _, hf⟩ := FiniteField.card (O ⧸ m) l
  have hf' : Nat.card (Padic.coefficientExtensionResidueField l E) = l ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hf
  obtain ⟨d, ⟨b⟩⟩ := Scheme.purTwistIntegralBasis l E
  obtain ⟨q⟩ := finite_basis_quotient l E d b 1
  have hcard : Nat.card (O ⧸ Ideal.span {(l : O)}) = l ^ d := by
    simpa only [pow_one, Nat.card_fun, Nat.card_fin, Nat.card_zmod] using
      Nat.card_congr q.toEquiv
  have hgen : Ideal.span ({π} : Set O) = m :=
    hO.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hI : Ideal.span {(l : O)} = m ^ P.ramificationIndex := by
    rw [← hgen, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.mpr (kummer_prime_power P).2
  have hp : m.IsPrime := inferInstance
  have hc := cardQuot_pow_of_prime (P := m) hO.2.2.2.2.2.2.2.2.2.1
    (i := P.ramificationIndex)
  simp only [Submodule.cardQuot_apply] at hc
  rw [← hI, hcard, hf', ← pow_mul] at hc
  have hd : d = P.ramificationIndex * (f : ℕ) := by
    simpa only [Nat.mul_comm] using
      Nat.pow_right_injective (Fact.out : l.Prime).two_le hc
  exact ⟨f, d, hf', hd, ⟨b⟩⟩

private theorem kummer_finite_basis (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (n N : ℕ)
    (hn : P.level = n + 1) (hN : P.kummerLevel = N + 1)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+*
      Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) :
    ∃ f : ℕ,
      Nat.card (Padic.coefficientExtensionResidueField P.coefficients.l P.extension) =
        P.coefficients.l ^ f ∧
      ∃ b : Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1) ≃+
          (Fin (P.ramificationIndex * f) → ZMod (P.coefficients.l ^ (N + 1))),
        ∀ (z : ZMod (P.coefficients.l ^ (N + 1)))
          (x : Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)),
          b (a z * x) = z • b x := by
  obtain ⟨f, d, hf, hd, ⟨b⟩⟩ := kummer_basis_rank P
  subst d
  obtain ⟨q⟩ := finite_basis_quotient P.coefficients.l P.extension _ b (N + 1)
  have hI : Padic.coefficientExtensionIdeal P.coefficients.l P.extension (n + 1) =
      Ideal.span {((P.coefficients.l : Padic.coefficientExtensionIntegers
        P.coefficients.l P.extension) ^ (N + 1))} := by
    rw [← hn]
    simpa only [exponent, hN, Nat.cast_pow] using kummer_ideal P h
  let e := (Ideal.quotEquivOfEq hI).toAddEquiv.trans q
  refine ⟨f, hf, e, ?_⟩
  intro z x
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast, ← zsmul_eq_mul, map_zsmul, Int.cast_smul_eq_zsmul]


private theorem tensorRestriction_tmul
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S) (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))
    {X Y : T.ProEtᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M).map i
      (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (SheafOfModules.exists_changeOfRingsMapMixedUniverses.{u, u + 1, u + 1,
    u + 1} c M i) s m

private noncomputable def scalarPresheafAdjunct
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj A)) (H : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (f : SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M ⟶ H.val) : M ⟶
      (SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u
        + 1} RingCat.{u
        + 1})).map c)).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{u + 1, u + 1,
      u + 1}
        (c.hom.app W).hom (X := M.val.obj W) (Y := H.val.obj W) (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul T, map_one] at h
        exact h }


private def scalarAdjunct (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (H : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (f : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} φ M ⟶ H) :
    M ⟶ (SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)).obj H :=
  scalarPresheafAdjunct T φ M H
    (PresheafOfModules.sheafificationHomEquiv (𝟙 _) f)

private theorem scalarAdjunct_injective (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (H : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) :
    Function.Injective (scalarAdjunct T φ M H) := by
  intro f g hfg
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).injective
  ext U : 1
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  exact congrArg (fun k ↦ k.val.app U m) hfg

private theorem kummer_comparison_unique (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n) (T : Scheme.{u})
    (α γ : P.kummerLine n T ≅ P.kummerRootsTensor n N a T)
    (hα : P.IsKummerComparison n N a T α) (hγ : P.IsKummerComparison n N a T γ) :
    γ = α := by
  apply Iso.ext
  apply scalarAdjunct_injective T (Scheme.purTwistIntegralQuotient T
    P.coefficients.l P.extension n)
  apply scalarAdjunct_injective T (Scheme.purTwistConstantIntegersMap T
    P.coefficients.l P.extension)
  ext U x
  change γ.hom.val.app U (P.kummerSourceTensor n T U.unop 1 1 x) =
    α.hom.val.app U (P.kummerSourceTensor n T U.unop 1 1 x)
  exact (hγ U.unop 1 1 x).trans (hα U.unop 1 1 x).symm

private theorem secondMap_comp {T : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}}
    (M : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    {N N' N'' : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)}
    (f : N ⟶ N') (g : N' ⟶ N'') :
    SheafOfModules.siteSheafTensorSecondMap M (f ≫ g) =
      SheafOfModules.siteSheafTensorSecondMap M f ≫
        SheafOfModules.siteSheafTensorSecondMap M g := by
  have h : SheafOfModules.siteTensorSecondMap M.val (f.val ≫ g.val) =
      SheafOfModules.siteTensorSecondMap M.val f.val ≫
        SheafOfModules.siteTensorSecondMap M.val g.val := by
    ext U : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl
  have hf : (f ≫ g).val = f.val ≫ g.val := rfl
  dsimp only [SheafOfModules.siteSheafTensorSecondMap]
  rw [hf, h, CategoryTheory.Functor.map_comp]

private theorem secondMap_id {T : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}}
    (M N : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    SheafOfModules.siteSheafTensorSecondMap M (𝟙 N) = 𝟙 _ := by
  have h : SheafOfModules.siteTensorSecondMap M.val (𝟙 N.val) = 𝟙 _ := by
    ext U : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl
  have hf : (𝟙 N : N ⟶ N).val = 𝟙 N.val := rfl
  dsimp only [SheafOfModules.siteSheafTensorSecondMap]
  rw [hf, h]
  exact CategoryTheory.Functor.map_id _ _

private theorem kummer_derived (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n) (T : Scheme.{u})
    (α : P.kummerLine n T ≅ P.kummerRootsTensor n N a T) :
    P.KummerDerivedCompatible n N a T α := by
  have h (M : Scheme.tateModules T (P.kummerCoefficient n)) :
      IsIso (SheafOfModules.siteSheafTensorSecondMap M α.hom) := by
    refine ⟨⟨SheafOfModules.siteSheafTensorSecondMap M α.inv, ?_, ?_⟩⟩
    · rw [← secondMap_comp, α.hom_inv_id, secondMap_id]
    · rw [← secondMap_comp, α.inv_hom_id, secondMap_id]
  intro K _
  let : ∀ i, IsIso ((((P.kummerTensorMap n N a T α).mapHomologicalComplex
      (ComplexShape.up ℤ)).app K).f i) := fun i ↦ h (K.X i)
  have := HomologicalComplex.Hom.isIso_of_components
    (((P.kummerTensorMap n N a T α).mapHomologicalComplex (ComplexShape.up ℤ)).app K)
  infer_instance


/-- Finite Kummer level, with arithmetic, explicit roots tensor, and both compatibilities.
Source: the current blueprint finite Kummer level statement and Stacks Tag 03PK
(blueprint: lem-pur-finite-kummer-level).

Proof: (1) use the DVR characterization of the chosen valuation ring and
uniformizer to identify the ramification index, the two power ideals and the
normalized logarithmic valuations. Compare powers of the irreducible uniformizer
to prove minimality of the killing exponent. (2) reduce a finite integral basis
modulo ell^k. The residue-field characteristic is ell. Comparing the cardinality
of the basis quotient with the cardinality of the maximal-ideal-power quotient
gives d=ef. Additive equivalences commute with integer scalars, giving the stated
Z/ell^k linearity for its unique scalar map. (3) apply the normalized projection
comparison of lem-pur-kummer-normalized-projection; two scalar-extension
adjunctions show that its pure-tensor formula determines it uniquely. (4) tensor
maps in the second variable preserve identities and composition, so tensoring
with this isomorphism is an isomorphism in every complex degree. The resulting
complex isomorphism is a quasi-isomorphism, including on every K-flat complex.
(5) lem-pur-kummer-normalized-base-change constructs the coordinate root-limit
map from the tower map and adjunction, then conjugates the finite-root tensor
base-change isomorphism by the two normalized comparisons. Their normalization
formulas prove the source-line formula and the commuting square. No arbitrary
basis defines the canonical sheaf comparison, and no preservation of an infinite
limit by inverse image is assumed.
-/
theorem finiteKummerLevel (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) :
    1 ≤ P.kummerLevel ∧
    P.level = P.ramificationIndex * P.kummerLevel ∧
    (-Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
      (P.coefficients.l : P.extension)) / Real.log P.coefficients.l = 1) ∧
    (-Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
      (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension).val) /
        Real.log P.coefficients.l = (P.ramificationIndex : ℝ)⁻¹) ∧
    (P.level : ℝ) *
      (-Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
        (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension).val) /
          Real.log P.coefficients.l) = P.kummerLevel ∧
    Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level =
      Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
        P.coefficients.l P.extension)} : Set (Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension)) ∧
    (∃ r : P.Ring ≃+* (Padic.coefficientExtensionIntegers P.coefficients.l P.extension ⧸
        Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension)} : Set (Padic.coefficientExtensionIntegers
            P.coefficients.l P.extension))),
      ∀ x : Padic.coefficientExtensionIntegers P.coefficients.l P.extension,
        r (Ideal.Quotient.mk
          (Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level) x) =
        Ideal.Quotient.mk (Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension)} : Set (Padic.coefficientExtensionIntegers
            P.coefficients.l P.extension))) x) ∧
    (P.exponent : P.Ring) = 0 ∧
    (∀ j : ℕ, ((P.coefficients.l ^ j : ℕ) : P.Ring) = 0 → P.kummerLevel ≤ j) ∧
    ∀ n : ℕ, P.level = n + 1 →
      ∃ N : ℕ, P.kummerLevel = N + 1 ∧
        ∃ a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n,
          ∃ f : ℕ,
            Nat.card (Padic.coefficientExtensionResidueField P.coefficients.l P.extension) =
              P.coefficients.l ^ f ∧
            (∃ b : P.kummerCoefficient n ≃+
                (Fin (P.ramificationIndex * f) → ZMod (P.coefficients.l ^ (N + 1))),
              ∀ (z : ZMod (P.coefficients.l ^ (N + 1))) (x : P.kummerCoefficient n),
                b (a z * x) = z • b x) ∧
            ∃ α : ∀ (T : Scheme.{u})
                (_hT : ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x)),
                P.kummerLine n T ≅ P.kummerRootsTensor n N a T,
              (∀ (T : Scheme.{u})
                (hT : ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x)),
                P.IsKummerComparison n N a T (α T hT) ∧
                (∀ γ : P.kummerLine n T ≅ P.kummerRootsTensor n N a T,
                  P.IsKummerComparison n N a T γ → γ = α T hT) ∧
                P.KummerDerivedCompatible n N a T (α T hT)) ∧
              P.KummerBaseChangeCompatible n N a α := by
  classical
  have hp := kummer_positive P h
  have hz : (P.exponent : P.Ring) = 0 := by
    exact congrArg ULift.down (P.exponent_coefficient_eq_zero h)
  refine ⟨hp.1, hp.2, kummer_log_prime P, kummer_log_uniformizer P, ?_,
    kummer_ideal P h, kummer_quotient P h, hz, kummer_minimal P h, ?_⟩
  · rw [kummer_log_uniformizer]
    have he : (P.ramificationIndex : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (kummer_prime_power P).1)
    have hlevel : (P.level : ℝ) = P.ramificationIndex * P.kummerLevel := by
      exact_mod_cast hp.2
    rw [hlevel]
    field_simp
  · intro n hn
    obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : P.kummerLevel ≠ 0)
    have ha : ((P.coefficients.l ^ (N + 1) : ℕ) : P.kummerCoefficient n) = 0 := by
      change ((P.coefficients.l ^ (N + 1) : ℕ) :
        Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) = 0
      rw [← hn]
      simpa only [exponent, hN] using hz
    let a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n :=
      ZMod.castHom (ringChar.dvd ha) _
    obtain ⟨f, hf, b, hb⟩ := kummer_finite_basis P h n N hn hN a
    have hI : Padic.coefficientExtensionIdeal P.coefficients.l P.extension (n + 1) =
        Ideal.span {((P.coefficients.l : Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension) ^ (N + 1))} := by
      rw [← hn]
      simpa only [exponent, hN, Nat.cast_pow] using kummer_ideal P h
    choose α hα using kummer_normalized_projection P n N hI a
    refine ⟨N, hN, a, f, hf, ⟨b, hb⟩, α, ?_,
      kummer_normalized_base_change P n N a α hα⟩
    intro T hT
    exact ⟨hα T hT, fun γ hγ ↦ kummer_comparison_unique P n N a T
      (α T hT) γ (hα T hT) hγ, kummer_derived P n N a T (α T hT)⟩

end WeilConjectures.PurityFiniteSetting
