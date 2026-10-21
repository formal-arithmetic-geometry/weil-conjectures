/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q6
-/
module

public import Sheaf.Paper.PurTwistCoefficientRings
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Sheaf.CategoryTheory.ConstantFiniteFreeSectionBasis

/-! # Finite coefficient extension and sheafwise completion

Source: coefficient-twist blueprint, order 1505, proof step 6.
(blueprint: lem-pur-twist-coefficient-tensor)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- The coefficient valuation ring is the finite integral closure of the base DVR.
This is the arithmetic finite-basis step in the proof below. -/
private theorem integral_basis (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ k : ℕ, Nonempty (@Module.Basis (Fin k) ℤ_[l]
        (Padic.coefficientExtensionIntegers l E) _ _
        (Module.compHom (Padic.coefficientExtensionIntegers l E) (purTwistIntegersMap l E))) := by
  classical
  let O := Padic.coefficientExtensionIntegers l E
  let : Algebra ℤ_[l] O := (purTwistIntegersMap l E).toAlgebra
  let : Algebra ℤ_[l] E := ((algebraMap ℚ_[l] E).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  have hmap (z : ℤ_[l]) : (purTwistIntegersMap l E z : E) =
      algebraMap ℚ_[l] E (z : ℚ_[l]) :=
    (purTwistIntegersMap_existsUnique l E).exists.choose_spec z
  let : IsScalarTower ℤ_[l] O E := IsScalarTower.of_algebraMap_eq fun z ↦ (hmap z).symm
  have hO := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : IsFractionRing O E := hO.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing O := hO.2.2.2.2.2.2.2.2.1
  have : IsIntegrallyClosedIn O E :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn E).mp inferInstance
  have hInt (x : E) : x ∈ O ↔ _root_.IsIntegral ℤ_[l] x := by
    constructor
    · intro hx
      have hmon := minpoly.monic (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) x)
      have hcoeff := (spectralValue_le_one_iff hmon).mp ((hO.1 x).mp hx)
      have hlift : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact ⟨⟨(minpoly ℚ_[l] x).coeff n, hcoeff n⟩, rfl⟩
      obtain ⟨q, hq, _, hqmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmon
      refine ⟨q, hqmon, ?_⟩
      change q.eval₂ ((algebraMap ℚ_[l] E).comp (algebraMap ℤ_[l] ℚ_[l])) x = 0
      rw [← Polynomial.eval₂_map, hq]
      exact minpoly.aeval ℚ_[l] x
    · intro hx
      have hx' : _root_.IsIntegral O x := hx.tower_top
      obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := O) (R := O)).mp hx'
      exact hy ▸ y.property
  let : IsIntegralClosure O ℤ_[l] E :=
    ⟨Subtype.val_injective, fun {x} ↦ by
      rw [← hInt]
      exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩⟩
  have : IsScalarTower ℤ_[l] ℚ_[l] E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite ℤ_[l] O := IsIntegralClosure.finite ℤ_[l] ℚ_[l] E O
  have : Module.IsTorsionFree ℤ_[l] E :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      ((algebraMap ℚ_[l] E).injective.comp
        (show Function.Injective (algebraMap ℤ_[l] ℚ_[l]) from Subtype.val_injective))
  have : Module.Free ℤ_[l] O := IsIntegralClosure.module_free ℤ_[l] ℚ_[l] E O
  exact ⟨Module.finrank ℤ_[l] O, ⟨Module.finBasis ℤ_[l] O⟩⟩

/-- The finite integral basis gives bases on the actual constant coefficient
section rings, including sections which are only locally constant. -/
private theorem coefficient_section_basis (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ (n : ℕ) (b : ∀ U : S.ProEtᵒᵖ,
      @Module.Basis (Fin n) ((purTwistZlConstant S l).obj.obj U)
        ((purTwistIntegralConstant S l E).obj.obj U) _ _
        (Module.compHom _ ((purTwistConstantIntegersMap S l E).hom.app U).hom)),
      ∀ (U V : S.ProEtᵒᵖ) (f : U ⟶ V)
        (s : (purTwistIntegralConstant S l E).obj.obj U) (i : Fin n),
        letI : Module ((purTwistZlConstant S l).obj.obj U)
            ((purTwistIntegralConstant S l E).obj.obj U) :=
          Module.compHom _ ((purTwistConstantIntegersMap S l E).hom.app U).hom
        letI : Module ((purTwistZlConstant S l).obj.obj V)
            ((purTwistIntegralConstant S l E).obj.obj V) :=
          Module.compHom _ ((purTwistConstantIntegersMap S l E).hom.app V).hom
        (b V).equivFun ((purTwistIntegralConstant S l E).obj.map f s) i =
          (purTwistZlConstant S l).obj.map f ((b U).equivFun s i) := by
  let := WeilConjectures.integralCoefficientRingSheafify.{u, u} S
  let := WeilConjectures.integralCoefficientAbSheafify.{u, u} S
  obtain ⟨k, ⟨b⟩⟩ := integral_basis l E
  let O := Padic.coefficientExtensionIntegers l E
  let : Module ℤ_[l] O := Module.compHom O (purTwistIntegersMap l E)
  let φ : ULift.{u + 1} ℤ_[l] →+* ULift.{u + 1} O :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((purTwistIntegersMap l E).comp ULift.ringEquiv.toRingHom)
  let : Algebra (ULift.{u + 1} ℤ_[l]) (ULift.{u + 1} O) := φ.toAlgebra
  let b' : Module.Basis (Fin k) (ULift.{u + 1} ℤ_[l]) (ULift.{u + 1} O) :=
    (b.map ULift.moduleEquiv.symm).mapCoeffs ULift.ringEquiv.symm (fun _ _ ↦ rfl)
  have : Module.Free (ULift.{u + 1} ℤ_[l]) (ULift.{u + 1} O) :=
    Module.Free.of_basis b'
  have : Module.Finite (ULift.{u + 1} ℤ_[l]) (ULift.{u + 1} O) :=
    Module.Finite.of_basis b'
  exact @CategoryTheory.constantFiniteFree_sectionBasis.{u + 1, u, 0}
    S.ProEt inferInstance (ProEt.topology S)
    (WeilConjectures.integralCoefficientRingSheafify.{u, u} S)
    (inferInstanceAs ((ProEt.topology S).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})))
    (WeilConjectures.integralCoefficientAbSheafify.{u, u} S)
    (purTwistAbLocallyBijective S)
    (CommRingCat.of (ULift.{u + 1} ℤ_[l])) (CommRingCat.of (ULift.{u + 1} O))
    inferInstance inferInstance inferInstance

/-- Finite freeness suffices for the tensor/completion map over any ring,
including the possibly non-Noetherian section rings used here. -/
private theorem finiteFreeCompletionTensor {R : Type v} [CommRing R] (I : Ideal R)
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    Function.Bijective (AdicCompletion.ofTensorProduct I M) := by
  classical
  let n := Fintype.card (Module.Free.ChooseBasisIndex R M)
  let b := (Module.Free.chooseBasis R M).reindex (Fintype.equivFin _)
  let e := b.equivFun
  let eT := LinearEquiv.baseChange R (AdicCompletion I R) M (Fin n → R) e
  let eC := AdicCompletion.congr I e
  have hnat (x : AdicCompletion I R ⊗[R] M) :
      eC (AdicCompletion.ofTensorProduct I M x) =
        AdicCompletion.ofTensorProduct I (Fin n → R) (eT x) :=
    LinearMap.congr_fun (AdicCompletion.ofTensorProduct_naturality I e.toLinearMap) x
  have hpi := AdicCompletion.ofTensorProduct_bijective_of_pi_of_fintype I
    (Fin n)
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply eT.injective
    apply hpi.injective
    exact (hnat x).symm.trans ((congrArg eC hxy).trans (hnat y))
  · intro y
    obtain ⟨z, hz⟩ := hpi.surjective (eC y)
    refine ⟨eT.symm z, eC.injective ?_⟩
    rw [hnat, LinearEquiv.apply_symm_apply]
    exact hz

/-- The l-adic and uniformizer-adic filtrations are cofinal: l itself is
associated to a positive power of the recorded uniformizer. -/
private theorem prime_uniformizer_power (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ e : ℕ, 0 < e ∧ ∃ v : (Padic.coefficientExtensionIntegers l E)ˣ,
      (l : Padic.coefficientExtensionIntegers l E) =
        v * Padic.coefficientExtensionUniformizer l E ^ e := by
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
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hirr
  refine ⟨e, Nat.pos_of_ne_zero ?_, v, hv⟩
  rintro rfl
  apply hnonunit
  rw [hv, pow_zero, mul_one]
  exact v.isUnit

/-- The two coefficient filtrations agree on a cofinal subsequence, with the
inclusion needed to reduce a later cofinal entry to an arbitrary exponent. -/
private theorem coefficient_filtrations (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ e : ℕ, 0 < e ∧
      (∀ r : ℕ,
        (Ideal.span ({(l : Padic.coefficientExtensionIntegers l E)} : Set _) : Ideal _) ^ r =
          Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set _) ^ (e * r)) ∧
      ∀ n : ℕ, ∃ r : ℕ, n ≤ e * r ∧
        (Ideal.span ({(l : Padic.coefficientExtensionIntegers l E)} : Set _) : Ideal _) ^ r ≤
          Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set _) ^ n := by
  obtain ⟨e, he, v, hv⟩ := prime_uniformizer_power l E
  have hI : Ideal.span ({(l : Padic.coefficientExtensionIntegers l E)} : Set _) =
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set _) ^ e := by
    rw [hv, Ideal.span_singleton_mul_left_unit v.isUnit, Ideal.span_singleton_pow]
  have hpow (r : ℕ) :
      (Ideal.span ({(l : Padic.coefficientExtensionIntegers l E)} : Set _) : Ideal _) ^ r =
        Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set _) ^ (e * r) := by
    rw [hI, pow_mul]
  refine ⟨e, he, hpow, fun n ↦ ⟨n, ?_, ?_⟩⟩
  · exact Nat.le_mul_of_pos_left n he
  · rw [hpow]
    exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n he)

/-- Restricting the positive-exponent quotient tower to multiples of a positive
integer preserves its limit, with the actual comparison to the subsequence. -/
private theorem cofinal_power_subsequence (e : ℕ) (he : 0 < e)
    {D : Type v} [Category.{w} D] (F : ℕᵒᵖ ⥤ D)
    [CategoryTheory.Limits.HasLimit F] :
    let f : ℕ →o ℕ :=
      ⟨fun n ↦ e * (n + 1) - 1, fun _ _ h ↦
        Nat.sub_le_sub_right (Nat.mul_le_mul_left e (Nat.add_le_add_right h 1)) 1⟩
    ∃ h : CategoryTheory.Limits.HasLimit (f.monotone.functor.op ⋙ F),
      letI := h
      ∃ i : CategoryTheory.Limits.limit (f.monotone.functor.op ⋙ F) ≅
          CategoryTheory.Limits.limit F,
        ∀ n : ℕ,
          i.inv ≫ CategoryTheory.Limits.limit.π (f.monotone.functor.op ⋙ F) (op n) =
            CategoryTheory.Limits.limit.π F (op (f n)) := by
  let f : ℕ →o ℕ :=
    ⟨fun n ↦ e * (n + 1) - 1, fun _ _ h ↦
      Nat.sub_le_sub_right (Nat.mul_le_mul_left e (Nat.add_le_add_right h 1)) 1⟩
  have : f.monotone.functor.Final := f.monotone.final_functor_iff.mpr fun n ↦
    ⟨n, by
      change n ≤ e * (n + 1) - 1
      have h := Nat.le_mul_of_pos_left (n + 1) he
      omega⟩
  refine ⟨inferInstance, Functor.Initial.limitIso f.monotone.functor.op F, ?_⟩
  intro n
  change CategoryTheory.Limits.limit.pre F f.monotone.functor.op ≫ _ = _
  exact CategoryTheory.Limits.limit.pre_π F f.monotone.functor.op (op n)

/-- The canonical balanced coefficient map, constructed from the two actual scalar
inclusions. Its pure-tensor formula is definitional.
Source: Stacks 03EK (blueprint: lem-pur-twist-coefficient-tensor). -/
noncomputable def purTwistCoefficientTensorMap (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (U : S.ProEtᵒᵖ) :
    letI := ((purTwistConstantIntegersMap S l E).hom.app U).hom.toAlgebra
    letI := ((purTwistZlCompletionMap S l).hom.app U).hom.toAlgebra
    ((purTwistIntegralConstant S l E).obj.obj U ⊗[
        (purTwistZlConstant S l).obj.obj U] (purTwistZlCompletion S l).obj.obj U) →+*
        (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S).obj.obj U :=
  let a := ((purTwistZlCompletionMap S l).hom.app U).hom
  let b := ((purTwistConstantIntegersMap S l E).hom.app U).hom
  let c := ((purTwistCompletedScalarMap S l E).hom.app U).hom
  let d := ((purTwistIntegralCompletionMap S l E).hom.app U).hom
  letI := b.toAlgebra
  letI := a.toAlgebra
  letI := (c.comp a).toAlgebra
  let f : (purTwistIntegralConstant S l E).obj.obj U →ₐ[
      (purTwistZlConstant S l).obj.obj U]
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S).obj.obj U :=
    { __ := d
      commutes' := fun z ↦ (ConcreteCategory.congr_hom
        (congrArg (fun t ↦ t.hom.app U) (purTwistCoefficientSquare S l E)) z).symm }
  let g : (purTwistZlCompletion S l).obj.obj U →ₐ[
      (purTwistZlConstant S l).obj.obj U]
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S).obj.obj U :=
    { __ := c
      commutes' := fun _ ↦ rfl }
  (Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _)).toRingHom

/-- Completion of the finite integral extension is the sectionwise scalar tensor.

Source: coefficient-twist blueprint, order 1505, proof step 6; Stacks Project,
Tag 03EK. (blueprint: lem-pur-twist-coefficient-tensor)

Proof: identify O_E with the integral closure of Z_l in E. An element of O_E
has monic minimal polynomial over Q_l with integral coefficients by the spectral
norm criterion, hence is integral over Z_l. Conversely integrality over Z_l
implies integrality over the integrally closed valuation ring O_E, hence membership
in O_E. Finiteness of integral closure over the complete DVR, and torsion freeness
in E, give a finite free Z_l-module. Choose a finite basis and its coordinate maps.
Constant sheafification transports the basis and its inverse to every section
ring, naturally under restriction. Reducing modulo l^r identifies the coefficient
modules with a finite power of Z/l^r. Limits commute with this finite power.
Writing l as a unit times a positive power of the chosen uniformizer identifies
the l-power quotient limit with the uniformizer-power quotient limit: a tuple
on the cofinal subsequence extends uniquely by reduction at any later index.
The resulting additive comparison on each object sends b tensor a to the product
of the two specified scalar inclusions. That formula makes it multiplicative
and unital; it agrees definitionally with purTwistCoefficientTensorMap. The
finite-basis inverse proves bijectivity. Pure tensors also prove compatibility
with restrictions. Rank zero and the zero section ring cause no exception: their
tensors and both limits are zero. No hypothesis on the characteristic of the
base scheme is used in this coefficient calculation.
-/
theorem purTwistCoefficientTensor (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (U : S.ProEtᵒᵖ) :
    letI := ((purTwistConstantIntegersMap S l E).hom.app U).hom.toAlgebra
    letI := ((purTwistZlCompletionMap S l).hom.app U).hom.toAlgebra
    Function.Bijective (purTwistCoefficientTensorMap S l E U) := by
  sorry


end AlgebraicGeometry.Scheme
