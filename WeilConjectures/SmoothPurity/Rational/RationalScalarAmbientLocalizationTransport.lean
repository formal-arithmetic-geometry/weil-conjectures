/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Rational.RationalScalarDerivedRestriction
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationFullSubcategory
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.LocalizedModule.Away

/-! # Transport of integral ambient trace through rational localization

This module isolates the denominator and normalized scalar-extension transport.
(blueprint: new-sf-rational-scalar-ambient-localization-transport).
-/

@[expose] public noncomputable section

/-! ### Semilinear base change to localized coefficients -/

section SemilinearTensor

open TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] {t : R} {b : S} {φ : R →+* S}
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- Multiplication by an element of `R` that becomes a unit in `A` is injective on any
`A`-module that is a scalar tower over `R`. -/
theorem smul_eq_zero_of_isUnit_algebraMap {A P : Type*} [CommRing A] [Algebra R A]
    [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P] {r : R}
    (hr : IsUnit (algebraMap R A r)) {y : P} (hy : r • y = 0) : y = 0 := by
  rwa [← algebraMap_smul A r y, hr.smul_eq_zero] at hy

/-- The additive map `Loc_t ⊗[R] M → Loc_b ⊗[S] N`, `a ⊗ m ↦ c a ⊗ u m`, induced by an
additive `φ`-semilinear map `u` and a ring map `c` of localizations extending `φ`. -/
noncomputable def Localization.Away.semilinearTensorMap
    (c : Localization.Away t →+* Localization.Away b)
    (hc : ∀ r : R, c (algebraMap R _ r) = algebraMap S _ (φ r))
    (u : M →+ N) (hu : ∀ (r : R) (m : M), u (r • m) = φ r • u m) :
    Localization.Away t ⊗[R] M →+ Localization.Away b ⊗[S] N :=
  TensorProduct.liftAddHom
    { toFun := fun a ↦ (TensorProduct.mk S (Localization.Away b) N (c a)).toAddMonoidHom.comp u
      map_zero' := by
        ext m
        simp
      map_add' := by
        intro a a'
        ext m
        simp }
    (fun r a m ↦ by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_comp,
        LinearMap.toAddMonoidHom_coe, Function.comp_apply, TensorProduct.mk_apply]
      rw [Algebra.smul_def, map_mul, hc, hu, ← Algebra.smul_def, TensorProduct.smul_tmul])

/-- The defining formula of `Localization.Away.semilinearTensorMap` on pure tensors. -/
@[simp] theorem Localization.Away.semilinearTensorMap_tmul
    (c : Localization.Away t →+* Localization.Away b)
    (hc : ∀ r : R, c (algebraMap R _ r) = algebraMap S _ (φ r))
    (u : M →+ N) (hu : ∀ (r : R) (m : M), u (r • m) = φ r • u m)
    (a : Localization.Away t) (m : M) :
    Localization.Away.semilinearTensorMap c hc u hu (a ⊗ₜ m) = c a ⊗ₜ u m :=
  TensorProduct.liftAddHom_tmul _ _ a m

/-- `Localization.Away.semilinearTensorMap` is `φ`-semilinear. -/
theorem Localization.Away.semilinearTensorMap_smul
    (c : Localization.Away t →+* Localization.Away b)
    (hc : ∀ r : R, c (algebraMap R _ r) = algebraMap S _ (φ r))
    (u : M →+ N) (hu : ∀ (r : R) (m : M), u (r • m) = φ r • u m)
    (r : R) (x : Localization.Away t ⊗[R] M) :
    Localization.Away.semilinearTensorMap c hc u hu (r • x) =
      φ r • Localization.Away.semilinearTensorMap c hc u hu x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [TensorProduct.smul_tmul', semilinearTensorMap_tmul, semilinearTensorMap_tmul,
      TensorProduct.smul_tmul', Algebra.smul_def, map_mul, hc, ← Algebra.smul_def]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- If `b ∣ φ t` and `u` is a bijective additive `φ`-semilinear map, then the induced map
`Loc_t ⊗[R] M → Loc_b ⊗[S] N` is bijective: inverting `t` inverts `b` on `S`-modules. -/
theorem Localization.Away.semilinearTensorMap_bijective
    (c : Localization.Away t →+* Localization.Away b)
    (hc : ∀ r : R, c (algebraMap R _ r) = algebraMap S _ (φ r))
    (u : M →+ N) (hu : ∀ (r : R) (m : M), u (r • m) = φ r • u m)
    (hd : b ∣ φ t) (hbij : Function.Bijective u) :
    Function.Bijective (Localization.Away.semilinearTensorMap c hc u hu) := by
  obtain ⟨s, hs⟩ := hd
  have ht (n : ℕ) : IsUnit (algebraMap R (Localization.Away t) (t ^ n)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit t).pow n
  have hb (n : ℕ) : IsUnit (algebraMap S (Localization.Away b) (b ^ n)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit b).pow n
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨n, m, hm⟩ := IsLocalizedModule.Away.surj
      (TensorProduct.mk R (Localization.Away t) M 1) t x
    have h1 : (1 : Localization.Away b) ⊗ₜ[S] u m = 0 := by
      have := semilinearTensorMap_tmul c hc u hu 1 m
      rw [map_one, ← TensorProduct.mk_apply, ← hm, semilinearTensorMap_smul, hx,
        smul_zero] at this
      exact this.symm
    rw [← TensorProduct.mk_apply, ← map_zero (TensorProduct.mk S (Localization.Away b) N 1)]
      at h1
    obtain ⟨k, hk⟩ := IsLocalizedModule.Away.exists_of_eq (r := b) h1
    rw [smul_zero] at hk
    have hmk : t ^ k • m = 0 := by
      apply hbij.1
      rw [hu, map_zero, map_pow, hs, mul_pow, mul_comm, mul_smul, hk, smul_zero]
    apply smul_eq_zero_of_isUnit_algebraMap (ht n)
    rw [hm, TensorProduct.mk_apply]
    apply smul_eq_zero_of_isUnit_algebraMap (ht k)
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hmk, TensorProduct.tmul_zero]
  · obtain ⟨n, z, hz⟩ := IsLocalizedModule.Away.surj
      (TensorProduct.mk S (Localization.Away b) N 1) b y
    obtain ⟨m, hm⟩ := hbij.2 (s ^ n • z)
    refine ⟨((IsLocalization.Away.invSelf (S := Localization.Away t) t) ^ n) ⊗ₜ m, ?_⟩
    rw [semilinearTensorMap_tmul, hm, ← sub_eq_zero]
    apply smul_eq_zero_of_isUnit_algebraMap (hb n)
    rw [smul_sub, hz, sub_eq_zero, TensorProduct.mk_apply, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul, ← mul_smul, ← mul_pow, ← hs, ← map_pow, ← TensorProduct.smul_tmul,
      Algebra.smul_def, ← hc, ← map_mul, map_pow (algebraMap R (Localization.Away t)), ← mul_pow,
      IsLocalization.Away.mul_invSelf, one_pow, map_one]

end SemilinearTensor
set_option autoImplicit false
universe u
open CategoryTheory

namespace CategoryTheory.ScalarLocalization

variable {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
  {p : R}

/-- Composition of pure tensors in a scalar localization. -/
theorem tmul_comp_tmul {K L M : ScalarLocalization R C p} (a b : Localization.Away p)
    (f : K.obj ⟶ L.obj) (g : L.obj ⟶ M.obj) :
    @Eq (K ⟶ M) ((a ⊗ₜ[R] f : K ⟶ L) ≫ (b ⊗ₜ[R] g : L ⟶ M)) ((b * a) ⊗ₜ[R] (f ≫ g)) :=
  composition_tmul R C p K.obj L.obj M.obj g f b a

/-- The inclusion of a localized full subcategory on pure tensors. -/
theorem fullSubcategoryInclusion_map_tmul (P : ObjectProperty C)
    {K M : ScalarLocalization R P.FullSubcategory p} (a : Localization.Away p)
    (f : K.obj ⟶ M.obj) :
    (fullSubcategoryInclusion R C P p).map (a ⊗ₜ[R] f : K ⟶ M) = a ⊗ₜ[R] f.hom :=
  TensorProduct.congr_tmul _ _ a f

/-- The inclusion of a localized full subcategory is additive. -/
instance fullSubcategoryInclusion_additive (P : ObjectProperty C) :
    (fullSubcategoryInclusion R C P p).Additive :=
  ⟨fun {_ _ f g} ↦ map_add (TensorProduct.congr _ _) f g⟩

end CategoryTheory.ScalarLocalization
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : AlgebraicGeometry.Scheme.{u})

/-- The uniformizer of `𝒪_F` divides the image of the uniformizer of `𝒪_E` under the
integer-ring inclusion induced by `ι`. -/
theorem coefficientExtensionUniformizer_dvd_integralScalarIntegerInclusion
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) :
    Padic.coefficientExtensionUniformizer l F ∣
      integralScalarIntegerInclusion l E F ι (Padic.coefficientExtensionUniformizer l E) := by
  have hE := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hL := (Padic.coefficientExtensionIntegers_dvr l F).choose_spec
  have hgenE : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hgenL : Ideal.span {Padic.coefficientExtensionUniformizer l F} =
      Padic.coefficientExtensionMaximalIdeal l F :=
    hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hπE : Padic.coefficientExtensionUniformizer l E ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    rw [← hgenE]
    exact Ideal.mem_span_singleton_self _
  have hπL : integralScalarIntegerInclusion l E F ι
      (Padic.coefficientExtensionUniformizer l E) ∈
      Padic.coefficientExtensionMaximalIdeal l F := by
    exact (hL.2.1 _).mpr
      ((integralScalar_absoluteValue l E F ι _).trans_lt ((hE.2.1 _).mp hπE))
  rwa [← hgenL, Ideal.mem_span_singleton] at hπL

/-- The localized coefficient map induced by `ι` extends the integer-ring inclusion. -/
theorem sfRationalCoefficientEquiv_symm_apply_algebraMap
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (r : Padic.coefficientExtensionIntegers l E) :
    (sfRationalCoefficientEquiv l F).symm (ι (sfRationalCoefficientEquiv l E
        (algebraMap _ (Localization.Away (Padic.coefficientExtensionUniformizer l E)) r))) =
      algebraMap _ (Localization.Away (Padic.coefficientExtensionUniformizer l F))
        (integralScalarIntegerInclusion l E F ι r) := by
  apply (sfRationalCoefficientEquiv l F).injective
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes]
  rfl

/-- The restricted completed scalar extension is additive. -/
theorem sfConstructibleIntegralScalarExtension_map_add
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (p : ℕ) (hl : l ≠ p) {X Y : sfIntegralConstructibleCategory l E W}
    (f g : X ⟶ Y) :
    (sfConstructibleIntegralScalarExtension p l hl E F ι W).map (f + g) =
      (sfConstructibleIntegralScalarExtension p l hl E F ι W).map f +
        (sfConstructibleIntegralScalarExtension p l hl E F ι W).map g := by
  apply ObjectProperty.hom_ext
  exact (integralScalarExtension l E F ι W).map_add

/-- The restricted completed scalar extension is semilinear along the integer-ring
inclusion. -/
theorem sfConstructibleIntegralScalarExtension_map_smul
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (p : ℕ) (hl : l ≠ p) {X Y : sfIntegralConstructibleCategory l E W}
    (a : Padic.coefficientExtensionIntegers l E) (f : X ⟶ Y) :
    (sfConstructibleIntegralScalarExtension p l hl E F ι W).map (a • f) =
      integralScalarIntegerInclusion l E F ι a •
        (sfConstructibleIntegralScalarExtension p l hl E F ι W).map f := by
  apply ObjectProperty.hom_ext
  exact ((integralScalarExtension l E F ι W).congr_map
    ((sfIntegralConstructible_linear l E W).1 a _ _ f.hom)).trans
    ((sfConstructibleIntegralScalarExtension_smul p l hl E F ι W X Y f a).trans
      ((sfIntegralConstructible_linear l F W).1 _ _ _ _).symm)

/-- A family of integral Hom equivalences from the actual derived restriction of `K`
to the completed integral scalar extension, indexed by integral constructible objects.
Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: new-sf-rational-scalar-ambient-localization-transport). -/
abbrev rationalScalarAmbientIntegralFamily
    (l : ℕ) [Fact l.Prime] (E F : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l F W)) :=
  ∀ M : sfIntegralConstructibleCategory l E W,
    ((rationalScalarDerivedRestriction l E F ι W).obj K ⟶ M.obj) ≃
      (K ⟶ ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E F ι W).obj M).obj)

/-- Postcomposition naturality of an integral family of Hom equivalences.
Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: new-sf-rational-scalar-ambient-localization-transport). -/
abbrev rationalScalarAmbientIntegralNaturality
    (l : ℕ) [Fact l.Prime] (E F : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l F W))
    (e₀ : rationalScalarAmbientIntegralFamily l E F ι W K) :=
  ∀ (M N : sfIntegralConstructibleCategory l E W) (f : M ⟶ N) (h),
    e₀ N (h ≫ f.hom) =
      e₀ M h ≫ ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E F ι W).map f).hom

/-- Inclusion of rational constructible objects into the ambient scalar localization
(the same expression as `rationalScalarAmbientInclusion` of the item module, which
cannot be imported here).
Source: the raw rationalization Hom formula
(blueprint: new-sf-rational-scalar-ambient-localization-transport). -/
abbrev rationalScalarAmbientTransportInclusion :=
  ScalarLocalization.fullSubcategoryInclusion (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory (scalarReductionSource l E W)) (sfIntegralConstructible l E W)
    (Padic.coefficientExtensionUniformizer l E)

/-- A natural family of integral Hom equivalences is semilinear along the integer-ring
inclusion: apply naturality to the scalar endomorphism `a • 𝟙`. -/
theorem rationalScalarAmbientIntegralFamily_apply_smul
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F)
    (K : DerivedCategory (scalarReductionSource l F W))
    (e₀ : rationalScalarAmbientIntegralFamily l E F ι W K)
    (he₀ : rationalScalarAmbientIntegralNaturality l E F ι W K e₀)
    (X : sfIntegralConstructibleCategory l E W) (a : Padic.coefficientExtensionIntegers l E)
    (h : (rationalScalarDerivedRestriction l E F ι W).obj K ⟶ X.obj) :
    e₀ X (a • h) = integralScalarIntegerInclusion l E F ι a • e₀ X h := by
  have key := he₀ X X (a • 𝟙 X) h
  have hX : (a • 𝟙 X).hom = a • 𝟙 X.obj := rfl
  have hY : (integralScalarIntegerInclusion l E F ι a • 𝟙
      ((sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E F ι W).obj X)).hom = integralScalarIntegerInclusion l E F ι a • 𝟙 _ := rfl
  rw [sfConstructibleIntegralScalarExtension_map_smul, CategoryTheory.Functor.map_id, hX,
    hY, Linear.comp_smul, Category.comp_id, Linear.comp_smul, Category.comp_id] at key
  exact key

/-- A natural family of integral Hom equivalences is additive: write `h₁ + h₂` as the
binary-product lift followed by the sum of the projections, using that integral
constructible objects are closed under binary products. -/
theorem rationalScalarAmbientIntegralFamily_apply_add
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F)
    (K : DerivedCategory (scalarReductionSource l F W))
    (e₀ : rationalScalarAmbientIntegralFamily l E F ι W K)
    (he₀ : rationalScalarAmbientIntegralNaturality l E F ι W K e₀)
    (X : sfIntegralConstructibleCategory l E W)
    (h₁ h₂ : (rationalScalarDerivedRestriction l E F ι W).obj K ⟶ X.obj) :
    e₀ X (h₁ + h₂) = e₀ X h₁ + e₀ X h₂ := by
  let P : sfIntegralConstructibleCategory l E W :=
    ⟨X.obj ⨯ X.obj, (sfIntegralConstructible l E W).prop_prod _ _ X.property X.property⟩
  let p₁ : P ⟶ X := ObjectProperty.homMk Limits.prod.fst
  let p₂ : P ⟶ X := ObjectProperty.homMk Limits.prod.snd
  have key := he₀ P X (p₁ + p₂) (Limits.prod.lift h₁ h₂)
  have hp : (p₁ + p₂).hom = Limits.prod.fst + Limits.prod.snd := rfl
  have hq (Z : sfIntegralConstructibleCategory l F W)
      (v w : (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E F ι W).obj P ⟶ Z) :
      (v + w).hom = v.hom + w.hom := rfl
  have hp₁ : p₁.hom = Limits.prod.fst := rfl
  have hp₂ : p₂.hom = Limits.prod.snd := rfl
  rw [sfConstructibleIntegralScalarExtension_map_add, hp, hq, Preadditive.comp_add,
    Preadditive.comp_add, ← he₀ P X p₁, ← he₀ P X p₂, hp₁, hp₂, Limits.prod.lift_fst,
    Limits.prod.lift_snd] at key
  exact key

set_option maxHeartbeats 400000 in
/-- Rationalized trace transport from the integral trace data.
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15, and the raw
scalar-localization Hom formula.
(blueprint: new-sf-rational-scalar-ambient-localization-transport).

Proof: tensor the integral equivalences with the localization coefficient ring,
then use the full-subcategory Hom equivalence on both sides. Pure tensors are
independent of their chosen denominators by balancing, and tensor induction
extends the calculation to all localized morphisms. The defining equations of
the normalized rational scalar extension identify the transported map with the
specified functor. Applying the same calculation to postcomposition proves the
displayed naturality equation. -/
theorem rationalScalarAmbientLocalizationTransport
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F)
    (K : DerivedCategory (scalarReductionSource l F W))
    (e₀ : rationalScalarAmbientIntegralFamily l E F ι W K)
    (he₀ : rationalScalarAmbientIntegralNaturality l E F ι W K e₀) :
    ∃ e : ∀ M : sfRationalConstructibleCategory l E W,
      (ScalarLocalization.mk ((rationalScalarDerivedRestriction l E F ι W).obj K) ⟶
        (rationalScalarAmbientTransportInclusion l E W).obj M) ≃
      (ScalarLocalization.mk K ⟶
        (rationalScalarAmbientTransportInclusion l F W).obj
          ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj M)),
      ∀ (M N : sfRationalConstructibleCategory l E W) (f : M ⟶ N) (h),
        e N (h ≫ (rationalScalarAmbientTransportInclusion l E W).map f) =
          e M h ≫ (rationalScalarAmbientTransportInclusion l F W).map
            ((sfRationalScalarExtension l E W 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).map f) := by
  let R := Padic.coefficientExtensionIntegers l E
  let t := Padic.coefficientExtensionUniformizer l E
  let φ := integralScalarIntegerInclusion l E F ι
  let hl := Nat.Prime.ne_zero (Fact.out : l.Prime)
  let Ext := sfConstructibleIntegralScalarExtension 0 l hl E F ι W
  let G := sfRationalScalarExtension l E W 0 hl F ι
  let ιE := rationalScalarAmbientTransportInclusion l E W
  let ιF := rationalScalarAmbientTransportInclusion l F W
  let c : Localization.Away t →+* Localization.Away (Padic.coefficientExtensionUniformizer l F) :=
    (sfRationalCoefficientEquiv l F).symm.toRingHom.comp
      (ι.toRingHom.comp (sfRationalCoefficientEquiv l E).toRingHom)
  have hc (r : R) : c (algebraMap R _ r) = algebraMap _ _ (φ r) :=
    sfRationalCoefficientEquiv_symm_apply_algebraMap l E F ι r
  have he₀_smul := rationalScalarAmbientIntegralFamily_apply_smul l E W F ι K e₀ he₀
  have he₀_add := rationalScalarAmbientIntegralFamily_apply_add l E W F ι K e₀ he₀
  let ψ (M : sfRationalConstructibleCategory l E W) :
      (ScalarLocalization.mk ((rationalScalarDerivedRestriction l E F ι W).obj K) ⟶ ιE.obj M) ≃+
        (ScalarLocalization.mk K ⟶ ιF.obj ⟨Ext.obj M.obj⟩) :=
    AddEquiv.ofBijective _ (Localization.Away.semilinearTensorMap_bijective c hc
      (AddMonoidHom.mk' (e₀ M.obj) (he₀_add M.obj)) (he₀_smul M.obj)
      (coefficientExtensionUniformizer_dvd_integralScalarIntegerInclusion l E F ι)
      (e₀ M.obj).bijective)
  have hobj (M : sfRationalConstructibleCategory l E W) :
      G.obj M = ⟨Ext.obj M.obj⟩ := sfRationalScalarExtension_obj l E W 0 hl F ι M
  have : G.Additive := sfRationalScalarExtension_additive l E W 0 hl F ι
  let Φ (M N : sfRationalConstructibleCategory l E W) :=
    Localization.Away.semilinearTensorMap c hc
      (AddMonoidHom.mk' (fun g : M.obj ⟶ N.obj ↦ Ext.map g)
        (fun g g' ↦ sfConstructibleIntegralScalarExtension_map_add l E W F ι 0 hl g g'))
      (fun a g ↦ sfConstructibleIntegralScalarExtension_map_smul l E W F ι 0 hl a g)
  have hG (M N : sfRationalConstructibleCategory l E W) (f : M ⟶ N) :
      G.map f = eqToHom (hobj M) ≫
        (Φ M N f : (⟨Ext.obj M.obj⟩ : sfRationalConstructibleCategory l F W) ⟶
          ⟨Ext.obj N.obj⟩) ≫ eqToHom (hobj N).symm := by
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul a g =>
      refine (conj_eqToHom_iff_heq _ _ (hobj M) (hobj N)).2 ?_
      refine (sfRationalScalarExtension_map_tmul l E W 0 hl F ι M.obj N.obj g a).trans
        (heq_of_eq ?_)
      exact (Localization.Away.semilinearTensorMap_tmul c hc
        (AddMonoidHom.mk' (fun g : M.obj ⟶ N.obj ↦ Ext.map g) _) _ a g).symm
    | add x y hx hy =>
      rw [G.map_add, hx, hy, map_add, Preadditive.add_comp, Preadditive.comp_add]
  have key (M N : sfRationalConstructibleCategory l E W) (f : M ⟶ N)
      (h : ScalarLocalization.mk ((rationalScalarDerivedRestriction l E F ι W).obj K) ⟶
        ιE.obj M) :
      ψ N (h ≫ ιE.map f) = ψ M h ≫ ιF.map (Φ M N f) := by
    have hψ (a : Localization.Away t)
        (h₀ : (rationalScalarDerivedRestriction l E F ι W).obj K ⟶ M.obj.obj) :
        ψ M (a ⊗ₜ h₀) = c a ⊗ₜ e₀ M.obj h₀ :=
      Localization.Away.semilinearTensorMap_tmul c hc _ (he₀_smul _) a h₀
    have hψ' (a : Localization.Away t)
        (h₀ : (rationalScalarDerivedRestriction l E F ι W).obj K ⟶ N.obj.obj) :
        ψ N (a ⊗ₜ h₀) = c a ⊗ₜ e₀ N.obj h₀ :=
      Localization.Away.semilinearTensorMap_tmul c hc _ (he₀_smul _) a h₀
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul a g =>
      induction h using TensorProduct.induction_on with
      | zero => simp
      | tmul a' h₀ =>
        have h1 : (a' ⊗ₜ h₀ : ScalarLocalization.mk
            ((rationalScalarDerivedRestriction l E F ι W).obj K) ⟶ ιE.obj M) ≫ ιE.map (a ⊗ₜ g) =
            ((a * a') ⊗ₜ (h₀ ≫ g.hom) : ScalarLocalization.mk
              ((rationalScalarDerivedRestriction l E F ι W).obj K) ⟶ ιE.obj N) := by
          rw [ScalarLocalization.fullSubcategoryInclusion_map_tmul]
          exact ScalarLocalization.tmul_comp_tmul (M := ιE.obj N) a' a h₀ g.hom
        have h2 : ιF.map (Φ M N (a ⊗ₜ g)) =
            (c a ⊗ₜ (Ext.map g).hom : ιF.obj ⟨Ext.obj M.obj⟩ ⟶ ιF.obj ⟨Ext.obj N.obj⟩) := by
          have hΦ : Φ M N (a ⊗ₜ g) = c a ⊗ₜ Ext.map g :=
            Localization.Away.semilinearTensorMap_tmul c hc _ _ a g
          rw [hΦ]
          exact ScalarLocalization.fullSubcategoryInclusion_map_tmul _ (c a) (Ext.map g)
        refine (congrArg (ψ N) h1).trans ((hψ' _ _).trans ?_)
        refine Eq.trans ?_ (congrArg₂ (· ≫ ·) (hψ a' h₀) h2).symm
        have h3 := ScalarLocalization.tmul_comp_tmul (K := ScalarLocalization.mk K)
          (L := ιF.obj ⟨Ext.obj M.obj⟩) (M := ιF.obj ⟨Ext.obj N.obj⟩) (c a') (c a)
          (e₀ M.obj h₀) (Ext.map g).hom
        have h4 : e₀ N.obj (h₀ ≫ g.hom) = e₀ M.obj h₀ ≫ (Ext.map g).hom := he₀ M.obj N.obj g h₀
        exact (congrArg₂ (fun x z ↦ (x ⊗ₜ z : ScalarLocalization.mk K ⟶ ιF.obj ⟨Ext.obj N.obj⟩))
          (map_mul c a a') h4).trans h3.symm
      | add x y hx hy => rw [Preadditive.add_comp, map_add, hx, hy, map_add, Preadditive.add_comp]
    | add x y hx hy =>
      rw [Functor.map_add, Preadditive.comp_add, map_add, hx, hy, map_add, Functor.map_add,
        Preadditive.comp_add]
  refine ⟨fun M ↦
    { toFun := fun h ↦ ψ M h ≫ ιF.map (eqToHom (hobj M).symm)
      invFun := fun h' ↦ (ψ M).symm (h' ≫ ιF.map (eqToHom (hobj M)))
      left_inv := fun h ↦ by
        beta_reduce
        rw [Category.assoc, ← ιF.map_comp, eqToHom_trans, eqToHom_refl, ιF.map_id,
          Category.comp_id, AddEquiv.symm_apply_apply]
      right_inv := fun h' ↦ by
        beta_reduce
        rw [AddEquiv.apply_symm_apply, Category.assoc, ← ιF.map_comp, eqToHom_trans,
          eqToHom_refl, ιF.map_id, Category.comp_id] }, ?_⟩
  intro M N f h
  rw [Equiv.coe_fn_mk, Equiv.coe_fn_mk, hG, key]
  simp [ιF]

end WeilConjectures
