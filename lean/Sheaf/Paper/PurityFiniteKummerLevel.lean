/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.IntrinsicCoefficientTwists
public import Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.SixFunctors.IntrinsicDerivedTensor
public import Sheaf.Paper.TateInverseLimitBaseChange
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.Module.ZMod
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.PurTwistSheafLocallyFree
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Mathlib.CategoryTheory.Limits.HasLimits
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

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
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The existing coefficient quotient at positive level n+1; this is only an index alias.
Source: finite Kummer level, coefficient notation (blueprint: lem-pur-finite-kummer-level). -/
abbrev kummerCoefficient (P : PurityFiniteSetting.{u}) (n : ℕ) :=
  Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)

/-- The existing coefficient ring sheaf at positive level n+1.
Source: finite Kummer level (blueprint: lem-pur-finite-kummer-level). -/
abbrev kummerRingSheaf (P : PurityFiniteSetting.{u}) (n : ℕ) (T : Scheme.{u}) :=
  integralCoefficientCommRingSheaf P.coefficients.l P.extension T n

/-- The existing finite twist O_E(1) tensor A, with the published constant-ring tensors.
Source: finite Kummer level (blueprint: lem-pur-finite-kummer-level). -/
abbrev kummerLine (P : PurityFiniteSetting.{u}) (n : ℕ) (T : Scheme.{u}) :=
  Scheme.purTwistFiniteOne T P.coefficients.l P.extension n

/-- The scalar map from Z/ell^(N+1) to A, applied to constant sheaves.
Source: finite Kummer level (blueprint: lem-pur-finite-kummer-level). -/
def kummerScalarMap (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n) (T : Scheme.{u}) :
    Scheme.purTwistFiniteRing T P.coefficients.l N ⟶ P.kummerRingSheaf n T :=
  (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (a.comp ULift.ringEquiv.toRingHom)))

/-- Exactly mu_(ell^(N+1)) tensor_(Z/ell^(N+1)) A, with its A-action.
The roots module is the recorded kernel of the power map, transported only through
commutation of constant sheaves with forgetting commutativity.
Source: finite Kummer level (blueprint: lem-pur-finite-kummer-level). -/
def kummerRootsTensor (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n) (T : Scheme.{u}) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (P.kummerScalarMap n N a T) (Scheme.purTwistRootsModule T P.coefficients.l N)

/-- The source's local tensor a tensor (b tensor x), using both published sheafifications.
Source: finite Kummer level (blueprint: lem-pur-finite-kummer-level). -/
def kummerSourceTensor (P : PurityFiniteSetting.{u}) (n : ℕ) (T : Scheme.{u})
    (U : T.ProEt)
    (a : (P.kummerRingSheaf n T).obj.obj (op U))
    (b : (Scheme.purTwistIntegralConstant T P.coefficients.l P.extension).obj.obj (op U))
    (x : (Scheme.purTwistZlOne T P.coefficients.l).obj.obj (op U)) :
    (P.kummerLine n T).val.obj (op U) :=
  Scheme.purScalarSection
    (Scheme.purTwistIntegralConstant T P.coefficients.l P.extension)
    (P.kummerRingSheaf n T)
    (Scheme.purTwistIntegralQuotient T P.coefficients.l P.extension n)
    (Scheme.purTwistIntegralOne T P.coefficients.l P.extension) U a
    (Scheme.purTwistIntegralTensor T P.coefficients.l P.extension (op U) b x)

/-- Pure tensors in the explicit finite roots scalar extension.
Source: finite Kummer level (blueprint: lem-pur-finite-kummer-level). -/
def kummerTargetTensor (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n) (T : Scheme.{u})
    (U : T.ProEt) (z : (P.kummerRingSheaf n T).obj.obj (op U))
    (y : (Scheme.proEtaleRootsOfUnitySheaf T (P.coefficients.l ^ (N + 1))).obj.obj
      (op U)) : (P.kummerRootsTensor n N a T).val.obj (op U) :=
  Scheme.purScalarSection (Scheme.purTwistFiniteRing T P.coefficients.l N)
    (P.kummerRingSheaf n T) (P.kummerScalarMap n N a T)
    (Scheme.purTwistRootsModule T P.coefficients.l N) U z y

/-- The canonical projection normalization, including the integral scalar in a tensor.
Source: finite Kummer level (blueprint: lem-pur-finite-kummer-level). -/
def IsKummerComparison (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n) (T : Scheme.{u})
    (α : P.kummerLine n T ≅ P.kummerRootsTensor n N a T) : Prop :=
  ∀ (U : T.ProEt) (z : (P.kummerRingSheaf n T).obj.obj (op U))
    (b : (Scheme.purTwistIntegralConstant T P.coefficients.l P.extension).obj.obj (op U))
    (x : (Scheme.purTwistZlOne T P.coefficients.l).obj.obj (op U)),
    α.hom.val.app (op U) (P.kummerSourceTensor n T U z b x) =
      P.kummerTargetTensor n N a T U
        (z * (Scheme.purTwistIntegralQuotient T P.coefficients.l P.extension n).hom.app
          (op U) b)
        ((limit.π (Scheme.proEtaleRootsOfUnityTower T P.coefficients.l
          (Fact.out : P.coefficients.l.Prime)) (op N)).hom.app (op U) x)

/-- The ordinary tensor comparison induced by the finite Kummer map on the second factor.
Source: finite Kummer level, derived tensor clause (blueprint: lem-pur-finite-kummer-level). -/
def kummerTensorMap (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n) (T : Scheme.{u})
    (α : P.kummerLine n T ≅ P.kummerRootsTensor n N a T) :=
  SheafOfModules.siteSheafTensorRightMap (A := P.kummerRingSheaf n T) α.hom

/-- Derived tensor compatibility on every K-flat representative. The ordinary natural
comparison is the second-factor map of the SAME normalized finite Kummer comparison.
Its termwise image on a K-flat complex is a quasi-isomorphism; this is precisely the
induced comparison K tensor^L A(1) to K tensor^L (mu tensor A).
Source: finite Kummer level, last sentence (blueprint: lem-pur-finite-kummer-level). -/
def KummerDerivedCompatible (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n) (T : Scheme.{u})
    (α : P.kummerLine n T ≅ P.kummerRootsTensor n N a T) : Prop :=
  ∀ K : CochainComplex (Scheme.tateModules T (P.kummerCoefficient n)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (R := P.kummerRingSheaf n T) K →
      QuasiIso (((P.kummerTensorMap n N a T α).mapHomologicalComplex
        (ComplexShape.up ℤ)).app K)

/-- The full base-change clause, on arbitrary scheme morphisms, with both vertical
comparisons fixed on inverse-image units. The root-limit map is fixed at EVERY level;
no assertion that inverse image commutes with infinite limits is assumed.
Source: finite Kummer level, final sentence (blueprint: lem-pur-finite-kummer-level). -/
def KummerBaseChangeCompatible (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n)
    (α : ∀ (T : Scheme.{u})
      (_hT : ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x)),
      P.kummerLine n T ≅ P.kummerRootsTensor n N a T) : Prop :=
  ∀ (T T' : Scheme.{u}) (f : T' ⟶ T)
    (hT : ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x))
    (hT' : ∀ x : T', IsUnit (P.coefficients.l : T'.presheaf.stalk x)),
    ∃ c : Scheme.purTwistZlOne T P.coefficients.l ⟶
        (Scheme.proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj
          (Scheme.purTwistZlOne T' P.coefficients.l),
      (∀ r : ℕ,
        c ≫ (Scheme.proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map
            (limit.π (Scheme.proEtaleRootsOfUnityTower T' P.coefficients.l
              (Fact.out : P.coefficients.l.Prime)) (op r)) =
          limit.π (Scheme.proEtaleRootsOfUnityTower T P.coefficients.l
            (Fact.out : P.coefficients.l.Prime)) (op r) ≫
              Scheme.proEtaleRootsOfUnityDirectImageMap f (P.coefficients.l ^ (r + 1))) ∧
      ∃ β : (Scheme.tatePullback f (P.kummerCoefficient n)).obj (P.kummerLine n T) ≅
          P.kummerLine n T',
        ∃ δ : (Scheme.tatePullback f (P.kummerCoefficient n)).obj
            (P.kummerRootsTensor n N a T) ≅ P.kummerRootsTensor n N a T',
          (∀ (U : T.ProEt) (z : (P.kummerRingSheaf n T).obj.obj (op U))
            (b : (Scheme.purTwistIntegralConstant T P.coefficients.l P.extension).obj.obj
              (op U))
            (x : (Scheme.purTwistZlOne T P.coefficients.l).obj.obj (op U)),
            β.hom.val.app (op ((Scheme.proEtaleBaseChange f).obj U))
                (Scheme.tateUnit f (P.kummerCoefficient n) (P.kummerLine n T) U
                  (P.kummerSourceTensor n T U z b x)) =
              P.kummerSourceTensor n T' ((Scheme.proEtaleBaseChange f).obj U)
                (Scheme.tateRingUnit f (P.kummerCoefficient n) U z)
                (Scheme.tateRingUnit f
                  (Padic.coefficientExtensionIntegers P.coefficients.l P.extension) U b)
                (c.hom.app (op U) x)) ∧
          (∀ (U : T.ProEt) (z : (P.kummerRingSheaf n T).obj.obj (op U))
            (y : (Scheme.proEtaleRootsOfUnitySheaf T (P.coefficients.l ^ (N + 1))).obj.obj
              (op U)),
            δ.hom.val.app (op ((Scheme.proEtaleBaseChange f).obj U))
                (Scheme.tateUnit f (P.kummerCoefficient n) (P.kummerRootsTensor n N a T) U
                  (P.kummerTargetTensor n N a T U z y)) =
              P.kummerTargetTensor n N a T' ((Scheme.proEtaleBaseChange f).obj U)
                (Scheme.tateRingUnit f (P.kummerCoefficient n) U z)
                ((Scheme.proEtaleRootsOfUnityDirectImageMap f
                  (P.coefficients.l ^ (N + 1))).hom.app (op U) y)) ∧
          (Scheme.tatePullback f (P.kummerCoefficient n)).map (α T hT).hom ≫ δ.hom =
            β.hom ≫ (α T' hT').hom

private theorem kummerBasisMod (p : ℕ) [Fact p.Prime] (O : Type u) [CommRing O]
    (φ : ℤ_[p] →+* O) (d N : ℕ)
    (b : @Module.Basis (Fin d) ℤ_[p] O _ _ (Module.compHom O φ)) :
    Nonempty ((O ⧸ Ideal.span {(p : O) ^ N}) ≃+ (Fin d → ZMod (p ^ N))) := by
  let := φ.toAlgebra
  have hsmul (x : O) : ((p : ℤ_[p]) ^ N) • x = (p : O) ^ N * x := by
    change φ ((p : ℤ_[p]) ^ N) * x = _
    rw [map_pow, map_natCast]
  let q : O →+ (Fin d → ZMod (p ^ N)) :=
    { toFun := fun x i ↦ PadicInt.toZModPow N (b.equivFun x i)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; simp }
  have hsurj : Function.Surjective q := by
    intro x
    choose y hy using fun i ↦ ZMod.ringHom_surjective (PadicInt.toZModPow N) (x i)
    refine ⟨b.equivFun.symm y, ?_⟩
    ext i
    exact (congrArg (fun z ↦ PadicInt.toZModPow N (z i))
      (b.equivFun.apply_symm_apply y)).trans (hy i)
  have hker : q.ker = (Ideal.span {(p : O) ^ N}).toAddSubgroup := by
    ext x
    change q x = 0 ↔ x ∈ Ideal.span {(p : O) ^ N}
    simp only [Ideal.mem_span_singleton]
    constructor
    · intro hx
      have hx' : ∀ i, (p : ℤ_[p]) ^ N ∣ b.equivFun x i := by
        intro i
        have hh : b.equivFun x i ∈ RingHom.ker (PadicInt.toZModPow N) :=
          congrFun hx i
        rwa [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hh
      choose y hy using hx'
      refine ⟨b.equivFun.symm y, ?_⟩
      symm
      apply b.equivFun.injective
      rw [← hsmul]
      change b.equivFun (((p : ℤ_[p]) ^ N) • b.equivFun.symm y) = b.equivFun x
      rw [map_smul, b.equivFun.apply_symm_apply]
      ext i
      exact (hy i).symm
    · rintro ⟨y, rfl⟩
      rw [← hsmul]
      ext i
      change PadicInt.toZModPow N (b.equivFun (((p : ℤ_[p]) ^ N) • y) i) = 0
      rw [map_smul]
      change PadicInt.toZModPow N ((p : ℤ_[p]) ^ N * b.equivFun y i) = 0
      rw [map_mul, map_pow, map_natCast]
      simp [← Nat.cast_pow]
  exact ⟨(QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective q hsurj)⟩

private theorem kummerDvrData (P : PurityFiniteSetting.{u}) :
    0 < P.ramificationIndex ∧
    Prime (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension) ∧
    Associated (P.coefficients.l : Padic.coefficientExtensionIntegers
      P.coefficients.l P.extension)
      (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension ^
        P.ramificationIndex) ∧
    Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
      (P.coefficients.l : P.extension) = (P.coefficients.l : ℝ)⁻¹ ∧
    (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
      (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension).val) ^
      P.ramificationIndex = (P.coefficients.l : ℝ)⁻¹ := by
  let l := P.coefficients.l
  let E := P.extension
  let O := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  have hs := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span {π} = Padic.coefficientExtensionMaximalIdeal l E :=
    hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have : IsLocalRing O := hs.2.2.2.1
  have : IsDiscreteValuationRing O := hs.2.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing O := hs.2.2.2.2.2.2.2.2.1
  have hmax : Padic.coefficientExtensionMaximalIdeal l E = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal hs.2.2.2.2.1
  have hirr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr (hmax ▸ hgen).symm
  have hl : (l : O) ≠ 0 := by
    intro hh
    have hh' : (l : E) = 0 := congrArg Subtype.val hh
    exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) hh'
  obtain ⟨k, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hirr
  have he : P.ramificationIndex = k := by
    unfold ramificationIndex
    change (emultiplicity π (l : O)).toNat = k
    rw [hv, emultiplicity_eq_of_associated_right
      (Associated.symm ⟨v, mul_comm _ _⟩),
      emultiplicity_pow_self hirr.ne_zero hirr.not_isUnit]
    simp
  have ha : Padic.coefficientExtensionAbsoluteValue l E (l : E) = (l : ℝ)⁻¹ := by
    change spectralNorm ℚ_[l] E (l : E) = _
    rw [← map_natCast (algebraMap ℚ_[l] E) l, spectralNorm_extends, Padic.norm_p]
  have hvab : Padic.coefficientExtensionAbsoluteValue l E ((v : O) : E) = 1 :=
    (hs.2.2.1 (v : O)).mp v.isUnit
  have hpow : (Padic.coefficientExtensionAbsoluteValue l E (π : E)) ^ k =
      (l : ℝ)⁻¹ := by
    have hh := congrArg (fun x : O ↦
      Padic.coefficientExtensionAbsoluteValue l E (x : E)) hv
    simpa only [Subring.coe_natCast, Subring.coe_mul, Subring.coe_pow, map_mul,
      map_pow, hvab, one_mul, ha] using hh.symm
  have hk : 0 < k := by
    by_contra hn
    have hk0 : k = 0 := by omega
    have hh : (l : ℝ)⁻¹ = 1 := by simpa [hk0] using hpow.symm
    have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have := inv_lt_one_of_one_lt₀ hl1
    linarith
  refine ⟨he ▸ hk, hirr.prime, ?_, ha, ?_⟩
  · rw [he]
    exact (Associated.symm ⟨v, by simpa [mul_comm] using hv.symm⟩)
  · simpa only [he] using hpow

private theorem kummerResidueRank (P : PurityFiniteSetting.{u}) :
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
  have hs := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : IsLocalRing O := hs.2.2.2.1
  have : IsDiscreteValuationRing O := hs.2.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing O := hs.2.2.2.2.2.2.2.2.1
  have : m.IsMaximal := hs.2.2.2.2.1
  have : Finite (O ⧸ m) := hs.2.2.2.2.2.2.2.2.2.2.2.1
  have hm0 : m ≠ ⊥ := hs.2.2.2.2.2.2.2.2.2.1
  have hgen : Ideal.span {π} = m := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  obtain ⟨he, hπ, hassoc, _⟩ := kummerDvrData P
  have hlm : (l : O) ∈ m := by
    apply (hs.2.1 _).2
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E), spectralNorm_extends]
    exact Padic.norm_p_lt_one
  let k := O ⧸ m
  let hkField : Field k := Ideal.Quotient.field m
  have hkChar : CharP k l := (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 (by
    change Ideal.Quotient.mk m (l : O) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hlm)
  let hkFintype : Fintype k := Fintype.ofFinite k
  obtain ⟨f, _hf, hcard⟩ := FiniteField.card k l
  have hcard' : Nat.card k = l ^ (f : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hEmpty : ∀ x : Scheme.empty.{u}, Invertible (l : Scheme.empty.residueField x) :=
    fun x ↦ PEmpty.elim x
  obtain ⟨d, ⟨b⟩⟩ :=
    (Scheme.pur_twist_sheaf_locally_free.{u, 0} Scheme.empty l E).2.2.1.1
  obtain ⟨e⟩ := kummerBasisMod l O (Scheme.purTwistIntegersMap l E) d 1 b
  have hcardO : Nat.card (O ⧸ Ideal.span {(l : O) ^ 1}) = l ^ d := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have hI : Ideal.span {(l : O) ^ 1} = m ^ P.ramificationIndex := by
    rw [pow_one, ← hgen, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.mpr hassoc
  have hcardpow : Nat.card (O ⧸ m ^ P.ramificationIndex) =
      Nat.card k ^ P.ramificationIndex :=
    cardQuot_pow_of_prime hm0
  have hd : d = P.ramificationIndex * (f : ℕ) := by
    have hp : l ^ d = l ^ ((f : ℕ) * P.ramificationIndex) := by
      rw [← hcardO, hI, hcardpow, hcard', pow_mul]
    have := (Nat.pow_right_injective (Fact.out : l.Prime).one_lt) hp
    simpa only [Nat.mul_comm] using this
  exact ⟨f, d, hcard', hd, ⟨b⟩⟩

private theorem kummerArithmetic (P : PurityFiniteSetting.{u})
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
    (∀ j : ℕ, ((P.coefficients.l ^ j : ℕ) : P.Ring) = 0 → P.kummerLevel ≤ j) := by
  obtain ⟨he, hπ, hassoc, hlab, hπab⟩ := kummerDvrData P
  have hn : P.level = P.ramificationIndex * P.kummerLevel :=
    (Nat.mul_div_cancel' h).symm
  have hN : 1 ≤ P.kummerLevel := by
    have := P.level_pos
    by_contra hh
    have hz : P.kummerLevel = 0 := by omega
    simp [hz] at hn
    omega
  have hl1 : (1 : ℝ) < P.coefficients.l := by
    exact_mod_cast (Fact.out : P.coefficients.l.Prime).one_lt
  have hlog : Real.log (P.coefficients.l : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos hl1)
  have hv : -Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l
      P.extension (Padic.coefficientExtensionUniformizer
        P.coefficients.l P.extension).val) / Real.log P.coefficients.l =
      (P.ramificationIndex : ℝ)⁻¹ := by
    have hh := congrArg Real.log hπab
    rw [Real.log_pow, Real.log_inv] at hh
    have he' : (P.ramificationIndex : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he)
    field_simp
    nlinarith [hh]
  have hI : Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level =
      Ideal.span {(P.exponent : Padic.coefficientExtensionIntegers
        P.coefficients.l P.extension)} := by
    rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow]
    apply Ideal.span_singleton_eq_span_singleton.mpr
    have hh := hassoc.pow_pow (n := P.kummerLevel)
    simpa only [← pow_mul, ← hn, exponent, Nat.cast_pow] using hh.symm
  have hz : (P.exponent : P.Ring) = 0 := by
    change Ideal.Quotient.mk _ (P.exponent : Padic.coefficientExtensionIntegers
      P.coefficients.l P.extension) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI ▸ Ideal.mem_span_singleton_self _)
  refine ⟨hN, hn, ?_, hv, ?_, hI, ?_, hz, ?_⟩
  · rw [hlab, Real.log_inv]
    field_simp
  · rw [hv, hn, Nat.cast_mul]
    have he' : (P.ramificationIndex : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he)
    field_simp
  · exact ⟨Ideal.quotEquivOfEq hI, fun x ↦ Ideal.quotEquivOfEq_mk hI x⟩
  · intro j hj
    change Ideal.Quotient.mk _ ((P.coefficients.l ^ j : ℕ) :
      Padic.coefficientExtensionIntegers P.coefficients.l P.extension) = 0 at hj
    have hdvd := Ideal.Quotient.eq_zero_iff_mem.mp hj
    rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, Nat.cast_pow] at hdvd
    have hh := le_emultiplicity_of_pow_dvd hdvd
    rw [emultiplicity_pow hπ,
      emultiplicity_eq_of_associated_right hassoc,
      emultiplicity_pow_self hπ.ne_zero hπ.not_isUnit] at hh
    have hh' : P.level ≤ j * P.ramificationIndex := by exact_mod_cast hh
    rw [hn] at hh'
    nlinarith

private theorem kummerCoefficientBasis (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (n N : ℕ)
    (hn : P.level = n + 1) (hN : P.kummerLevel = N + 1) :
    ∃ a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n,
      ∃ f : ℕ,
        Nat.card (Padic.coefficientExtensionResidueField P.coefficients.l P.extension) =
          P.coefficients.l ^ f ∧
        (∃ b : P.kummerCoefficient n ≃+
            (Fin (P.ramificationIndex * f) → ZMod (P.coefficients.l ^ (N + 1))),
          ∀ (z : ZMod (P.coefficients.l ^ (N + 1))) (x : P.kummerCoefficient n),
            b (a z * x) = z • b x) := by
  classical
  obtain ⟨f, d, hf, hd, ⟨b⟩⟩ := kummerResidueRank P
  obtain ⟨hpos, hlev, hvell, hvpi, hvn, hI, hr, hz, hmin⟩ := kummerArithmetic P h
  have hI' : Padic.coefficientExtensionIdeal P.coefficients.l P.extension (n + 1) =
      Ideal.span {(P.coefficients.l : Padic.coefficientExtensionIntegers
        P.coefficients.l P.extension) ^ (N + 1)} := by
    simpa only [hn, exponent, hN, Nat.cast_pow] using hI
  have hz' : ((P.coefficients.l ^ (N + 1) : ℕ) : P.kummerCoefficient n) = 0 := by
    change Ideal.Quotient.mk _ ((P.coefficients.l ^ (N + 1) : ℕ) :
      Padic.coefficientExtensionIntegers P.coefficients.l P.extension) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hI', Nat.cast_pow]
    exact Ideal.mem_span_singleton_self _
  let a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n :=
    ZMod.castHom (ringChar.dvd hz') _
  obtain ⟨e⟩ := kummerBasisMod P.coefficients.l _
    (Scheme.purTwistIntegersMap P.coefficients.l P.extension) d (N + 1) b
  let e' : P.kummerCoefficient n ≃+ (Fin d → ZMod (P.coefficients.l ^ (N + 1))) :=
    (Ideal.quotEquivOfEq hI').toAddEquiv.trans e
  subst d
  refine ⟨a, f, hf, e', ?_⟩
  intro z x
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast, ← zsmul_eq_mul, map_zsmul, Int.cast_smul_eq_zsmul]


/-- The geometric finite-level comparison and its compatibilities, after the arithmetic and
coefficient-basis clauses have been established. This is the separate sheaf-theoretic part
of the finite Kummer level argument.

Proof: construct the root-limit map by the inverse-limit universal property from the
coordinatewise root direct-image maps. Use the representable root scheme and its etale
base-change isomorphism to obtain the finite root comparisons. Tensor the normalized
projection with the finite coefficient map; local pure tensors determine the morphism and
prove uniqueness. The tensor map induced by an isomorphism is an isomorphism on every
K-flat complex. The constant two-term resolution and the finite free coefficient basis
identify ordinary and derived reduction. Pulling the root map and scalar maps through
base change gives the two vertical isomorphisms, and equality on local pure tensors proves
the commuting square. These are exactly blueprint steps (3)--(5).
Source: finite Kummer level blueprint, steps (3)--(5)
(blueprint: lem-pur-finite-kummer-level-geometric). -/
theorem finiteKummerLevel_geometric (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (n : ℕ) (hn : P.level = n + 1)
    (N : ℕ) (hN : P.kummerLevel = N + 1)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n)
    (f : ℕ)
    (hf : Nat.card (Padic.coefficientExtensionResidueField P.coefficients.l P.extension) =
      P.coefficients.l ^ f)
    (b : P.kummerCoefficient n ≃+
      (Fin (P.ramificationIndex * f) → ZMod (P.coefficients.l ^ (N + 1)))) :
    (∀ (z : ZMod (P.coefficients.l ^ (N + 1))) (x : P.kummerCoefficient n),
      b (a z * x) = z • b x) →
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
  sorry

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
  obtain ⟨hpos, hlev, hvell, hvpi, hvn, hI, hr, hz, hmin⟩ := kummerArithmetic P h
  refine ⟨hpos, hlev, hvell, hvpi, hvn, hI, hr, hz, hmin, ?_⟩
  intro n hn
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : P.kummerLevel ≠ 0)
  obtain ⟨a, f, hf, b, hb⟩ := kummerCoefficientBasis P h n N hn hN
  refine ⟨N, hN, a, f, hf, ⟨b, hb⟩, ?_⟩
  exact finiteKummerLevel_geometric P h n hn N hN a f hf b hb

end WeilConjectures.PurityFiniteSetting
