/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Sections of the twisting sheaves on the standard opens of projective space
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace MvPolynomial

open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : Type*} [Fintype n] (R : Type*) [CommRing R]

/-- The monomial `∏ᵢ Xᵢ ^ aᵢ` with coefficient `1`, for an exponent vector `a : n → ℤ`, the
negative exponents being read as `0`. -/
noncomputable def monomialToNat (a : n → ℤ) : MvPolynomial n R :=
  monomial (Finsupp.equivFunOnFinite.symm fun i ↦ (a i).toNat) 1

variable {R}

lemma monomialToNat_mul {a b : n → ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    monomialToNat R a * monomialToNat R b = monomialToNat R (a + b) := by
  rw [monomialToNat, monomialToNat, monomialToNat, monomial_mul, one_mul]
  congr 2
  ext i
  simp [Int.toNat_add (ha i) (hb i)]

lemma monomialToNat_pow {a : n → ℤ} (ha : 0 ≤ a) (k : ℕ) :
    monomialToNat R a ^ k = monomialToNat R (k • a) := by
  induction k with
  | zero =>
    rw [pow_zero, zero_smul, monomialToNat]
    have : (Finsupp.equivFunOnFinite.symm fun i ↦ ((0 : n → ℤ) i).toNat) = 0 := by
      ext i
      simp
    rw [this, ← C_1, C_apply]
  | succ k ih =>
    rw [pow_succ, ih, monomialToNat_mul (nsmul_nonneg ha k) ha, succ_nsmul]

lemma monomialToNat_mem (a : n → ℤ) :
    monomialToNat R a ∈ homogeneousSubmodule n R (∑ i, (a i).toNat) := by
  rw [mem_homogeneousSubmodule]
  refine isHomogeneous_monomial _ ?_
  rw [Finsupp.degree_eq_sum]
  simp

lemma monomialToNat_mem_of_sum {a : n → ℤ} (ha : 0 ≤ a) {k : ℕ} (h : ∑ i, a i = k) :
    monomialToNat R a ∈ homogeneousSubmodule n R k := by
  convert monomialToNat_mem (R := R) a
  zify
  rw [← h]
  exact Finset.sum_congr rfl fun i _ ↦ (Int.toNat_of_nonneg (ha i)).symm

section Away

omit [Fintype n] in
lemma val_sum {x : Submonoid (MvPolynomial n R)} {ι : Type*} (t : Finset ι)
    (f : ι → HomogeneousLocalization (homogeneousSubmodule n R) x) :
    (∑ i ∈ t, f i).val = ∑ i ∈ t, (f i).val :=
  map_sum (algebraMap (HomogeneousLocalization (homogeneousSubmodule n R) x) (Localization x)) f t

variable (s : Set n) (m : ℤ)

/-- The exponent vectors `e : n → ℤ` with `∑ eᵢ = m` and `eᵢ ≥ 0` for `i ∉ s`: the exponents of
the Laurent monomials of degree `m` whose denominators only involve the variables `Xᵢ`,
`i ∈ s`. -/
def laurentExponents : Set (n → ℤ) := {e | ∑ i, e i = m ∧ ∀ i ∉ s, 0 ≤ e i}

omit [Fintype n] in
lemma indicator_one_nonneg : 0 ≤ s.indicator (1 : n → ℤ) := fun i ↦ by
  by_cases h : i ∈ s <;> simp [h]

/-- The degree `|s|` of the monomial `∏_{i ∈ s} Xᵢ`. -/
noncomputable abbrev indicatorDegree : ℕ := ∑ i, (s.indicator (1 : n → ℤ) i).toNat

lemma cast_indicatorDegree : (indicatorDegree s : ℤ) = ∑ i, s.indicator (1 : n → ℤ) i := by
  push_cast
  exact Finset.sum_congr rfl fun i _ ↦ Int.toNat_of_nonneg (indicator_one_nonneg s i)

variable (R) in
lemma monomialToNat_indicator_mem :
    monomialToNat R (s.indicator 1) ∈ homogeneousSubmodule n R (indicatorDegree s) :=
  monomialToNat_mem _

/-- The number `∑ᵢ max(-eᵢ, 0)`, large enough that `e + N • 1_s ≥ 0` for `e` nonnegative
outside `s`. -/
def negPart (e : n → ℤ) : ℕ := ∑ i, (-e i).toNat

variable {s m}

omit [Fintype n] in
lemma add_nsmul_indicator_nonneg {e : n → ℤ} (he : ∀ i ∉ s, 0 ≤ e i) {N : ℕ}
    (hN : ∀ i, -e i ≤ N) : 0 ≤ e + N • s.indicator (1 : n → ℤ) := by
  intro i
  by_cases hi : i ∈ s
  · simp [Set.indicator_of_mem hi]
    linarith [hN i]
  · simp [Set.indicator_of_notMem hi, he i hi]

lemma neg_le_negPart (e : n → ℤ) (i : n) : -e i ≤ negPart e := by
  have h : (-e i).toNat ≤ negPart e :=
    Finset.single_le_sum (f := fun j ↦ (-e j).toNat) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)
  have := Int.self_le_toNat (-e i)
  omega

lemma sum_add_nsmul_indicator {e : n → ℤ} (he : ∑ i, e i = 0) (N : ℕ) :
    ∑ i, (e + N • s.indicator (1 : n → ℤ)) i = ((N • indicatorDegree s : ℕ) : ℤ) := by
  rw [smul_eq_mul, Nat.cast_mul, cast_indicatorDegree, Finset.mul_sum]
  simp only [Pi.add_apply, Finset.sum_add_distrib, he, zero_add, nsmul_eq_mul, Pi.mul_apply,
    Pi.natCast_apply]

lemma monomialToNat_add_nsmul_indicator_mem {e : n → ℤ} (he : e ∈ laurentExponents s 0)
    {N : ℕ} (hN : ∀ i, -e i ≤ N) :
    monomialToNat R (e + N • s.indicator 1) ∈
      homogeneousSubmodule n R (N • indicatorDegree s) :=
  monomialToNat_mem_of_sum (add_nsmul_indicator_nonneg he.2 hN) (sum_add_nsmul_indicator he.1 N)

variable (R s) in
/-- **The Laurent monomial `xᵉ`** in the degree-zero part of the localization of
`R[Xᵢ : i ∈ n]` away from `∏_{i ∈ s} Xᵢ`, for an exponent vector `e` with `∑ eᵢ = 0` and
`eᵢ ≥ 0` for `i ∉ s`: the fraction `x^{e + N 1_s} / (∏_{i ∈ s} Xᵢ)^N` for `N` large. -/
noncomputable def awayMonomial (e : laurentExponents s 0) :
    Away (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1)) :=
  Away.mk _ (monomialToNat_indicator_mem R s) (negPart e.1)
    (monomialToNat R (e.1 + negPart e.1 • s.indicator 1))
    (monomialToNat_add_nsmul_indicator_mem e.2 (neg_le_negPart e.1))

/-- `awayMonomial` may be computed with any large enough power of the denominator. -/
lemma awayMonomial_eq (e : laurentExponents s 0) {N : ℕ} (hN : ∀ i, -e.1 i ≤ N) :
    Away.mk _ (monomialToNat_indicator_mem R s) N (monomialToNat R (e.1 + N • s.indicator 1))
      (monomialToNat_add_nsmul_indicator_mem e.2 hN) = awayMonomial R s e := by
  have h0 := indicator_one_nonneg s
  refine Away.mk_eq_mk_of_mul_pow_eq (𝒜 := homogeneousSubmodule n R)
    (monomialToNat_indicator_mem R s) _ _ ?_
  rw [monomialToNat_pow h0, monomialToNat_pow h0,
    monomialToNat_mul (add_nsmul_indicator_nonneg e.2.2 hN) (nsmul_nonneg h0 _),
    monomialToNat_mul (add_nsmul_indicator_nonneg e.2.2 (neg_le_negPart e.1))
      (nsmul_nonneg h0 _)]
  congr 1
  rw [add_assoc, add_assoc, ← add_nsmul, ← add_nsmul, add_comm N]

/-- The value of `∑ⱼ gⱼ • x^{eⱼ}` in the localization, all Laurent monomials being written with
the same denominator. -/
lemma val_sum_smul_awayMonomial (t : Finset (laurentExponents s 0))
    (g : laurentExponents s 0 → R) {N : ℕ} (hN : ∀ e ∈ t, ∀ i, -e.1 i ≤ N) :
    (∑ e ∈ t, g e • awayMonomial R s e).val =
      Localization.mk (∑ e ∈ t, C (g e) * monomialToNat R (e.1 + N • s.indicator 1))
        ⟨monomialToNat R (s.indicator 1) ^ N, by use N⟩ := by
  rw [Localization.mk_sum, val_sum]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  rw [val_smul, ← awayMonomial_eq e (hN e he),
    Away.val_mk, Localization.smul_mk, smul_eq_C_mul]

/-- **The Laurent monomials `xᵉ` are linearly independent** in the degree-zero part of the
localization of `R[Xᵢ : i ∈ n]` away from `∏_{i ∈ s} Xᵢ`. -/
theorem linearIndependent_awayMonomial : LinearIndependent R (awayMonomial R s) := by
  classical
  rw [linearIndependent_iff']
  intro t g hg e₀ he₀
  have h0 := indicator_one_nonneg s
  set N := ∑ e ∈ t, negPart e.1
  have hN : ∀ e ∈ t, ∀ i, -e.1 i ≤ N := fun e he i ↦ (neg_le_negPart e.1 i).trans
    (Nat.cast_le.2 (Finset.single_le_sum (f := fun e : laurentExponents s 0 ↦ negPart e.1)
      (fun _ _ ↦ Nat.zero_le _) he))
  have hv := congrArg HomogeneousLocalization.val hg
  rw [val_sum_smul_awayMonomial t g hN, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hv
  obtain ⟨⟨c, k, rfl⟩, hk⟩ := hv
  dsimp only at hk
  have hnn : ∀ e ∈ t, 0 ≤ e.1 + (N + k) • s.indicator (1 : n → ℤ) := fun e he ↦
    add_nsmul_indicator_nonneg e.2.2 fun i ↦ (hN e he i).trans (by push_cast; omega)
  let u : laurentExponents s 0 → n →₀ ℕ := fun e ↦
    Finsupp.equivFunOnFinite.symm fun i ↦ ((e.1 + (N + k) • s.indicator (1 : n → ℤ)) i).toNat
  have hk' : ∑ e ∈ t, monomial (u e) (g e) = 0 := by
    rw [← hk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he ↦ ?_
    have hexp : k • s.indicator (1 : n → ℤ) + (e.1 + N • s.indicator 1) =
        e.1 + (N + k) • s.indicator 1 := by
      rw [add_nsmul]
      abel
    rw [monomialToNat_pow h0, mul_left_comm, monomialToNat_mul (nsmul_nonneg h0 k)
      (add_nsmul_indicator_nonneg e.2.2 (hN e he)), hexp, monomialToNat, C_mul_monomial, mul_one]
  have hu : ∀ e ∈ t, u e = u e₀ → e = e₀ := fun e he h ↦ Subtype.ext (funext fun i ↦ by
    have hi := congr($(h) i)
    simp only [u, Finsupp.coe_equivFunOnFinite_symm] at hi
    have h1 := Int.toNat_of_nonneg (hnn e he i)
    have h2 := Int.toNat_of_nonneg (hnn e₀ he₀ i)
    have h3 : (e.1 + (N + k) • s.indicator (1 : n → ℤ)) i =
        (e₀.1 + (N + k) • s.indicator (1 : n → ℤ)) i := by
      omega
    simpa using h3)
  have := congrArg (coeff (u e₀)) hk'
  rw [coeff_sum, coeff_zero, Finset.sum_eq_single e₀ (fun e he hne ↦ by
    rw [coeff_monomial, if_neg fun h ↦ hne (hu e he h)]) (fun h ↦ (h he₀).elim),
    coeff_monomial, if_pos rfl] at this
  exact this

/-- **The Laurent monomials `xᵉ` span** the degree-zero part of the localization of
`R[Xᵢ : i ∈ n]` away from `∏_{i ∈ s} Xᵢ`: a fraction `a / (∏_{i ∈ s} Xᵢ)^N` with `a` homogeneous
of degree `N |s|` is the sum of the fractions of the monomials of `a`. -/
theorem span_awayMonomial : Submodule.span R (Set.range (awayMonomial R s)) = ⊤ := by
  classical
  refine eq_top_iff.2 fun z _ ↦ ?_
  obtain ⟨N, a, ha, rfl⟩ := Away.mk_surjective _ (monomialToNat_indicator_mem R s) z
  have hdeg : ∀ u ∈ a.support, ∑ i, (u i : ℤ) = N * ∑ i, s.indicator (1 : n → ℤ) i := by
    intro u hu
    have h := ((mem_homogeneousSubmodule _ _).1 ha) (mem_support_iff.1 hu)
    replace h : u.degree = N • indicatorDegree s := (congrFun (congrArg DFunLike.coe Finsupp.degree_eq_weight_one) u).trans h
    rw [Finsupp.degree_eq_sum] at h
    rw [← cast_indicatorDegree, ← Nat.cast_mul, ← smul_eq_mul, ← h]
    push_cast
    rfl
  let e : a.support → laurentExponents s 0 := fun u ↦
    ⟨fun i ↦ (u.1 i : ℤ) - N * s.indicator 1 i, by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hdeg u.1 u.2, sub_self], fun i hi ↦ by
      simp [Set.indicator_of_notMem hi]⟩
  have key : ∀ u : a.support, ∃ h, Away.mk _ (monomialToNat_indicator_mem R s) N
      (monomial u.1 (1 : R)) h = awayMonomial R s (e u) := by
    intro u
    have hN : ∀ i, -(e u).1 i ≤ N := fun i ↦ by
      have : s.indicator (1 : n → ℤ) i ≤ 1 := by by_cases h : i ∈ s <;> simp [h]
      have : (0 : ℤ) ≤ N := Nat.cast_nonneg N
      simp only [e]
      nlinarith [Int.natCast_nonneg (u.1 i)]
    have hmono : monomialToNat R ((e u).1 + N • s.indicator 1) = monomial u.1 1 := by
      rw [monomialToNat]
      congr 1
      ext i
      simp [e]
    refine ⟨hmono ▸ monomialToNat_add_nsmul_indicator_mem (e u).2 hN, ?_⟩
    rw [← awayMonomial_eq (e u) hN]
    congr 1
    exact hmono.symm
  have hz : Away.mk _ (monomialToNat_indicator_mem R s) N a ha =
      ∑ u ∈ a.support.attach, coeff u.1 a • awayMonomial R s (e u) := by
    apply HomogeneousLocalization.val_injective
    rw [val_sum, Away.val_mk]
    conv_lhs => rw [a.as_sum]
    rw [← Finset.sum_attach, Localization.mk_sum]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    obtain ⟨h, hu⟩ := key u
    rw [val_smul, ← hu, Away.val_mk, Localization.smul_mk, smul_monomial, smul_eq_mul, mul_one]
  rw [hz]
  exact Submodule.sum_mem _ fun u _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

variable (R s) in
/-- **The monomial basis** of the degree-zero part of the localization of `R[Xᵢ : i ∈ n]` away
from `∏_{i ∈ s} Xᵢ`: the Laurent monomials `xᵉ` with `∑ eᵢ = 0` and `eᵢ ≥ 0` for `i ∉ s`. -/
noncomputable def awayMonomialBasis :
    Module.Basis (laurentExponents s 0) R
      (Away (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1))) :=
  .mk linearIndependent_awayMonomial span_awayMonomial.ge

@[simp]
lemma awayMonomialBasis_apply (e : laurentExponents s 0) :
    awayMonomialBasis R s e = awayMonomial R s e :=
  Module.Basis.mk_apply _ _ _

end Away

end MvPolynomial

namespace CommRingCat

set_option backward.isDefEq.respectTransparency false in
/-- **Bases are preserved by pushouts over the integers**: given a pushout square of commutative
rings `R → A, R → B, A → X, B → X` with `R` a quotient of `ℤ`, a `ℤ`-basis `v` of `A` maps to a
`B`-basis of `X`, i.e. every element of `X` is uniquely a finite sum `∑ b(cᵢ) a(vᵢ)`. -/
theorem IsPushout.bijective_sum_mul {R A B X : CommRingCat.{u}} {f : R ⟶ A} {g : R ⟶ B}
    {a : A ⟶ X} {b : B ⟶ X} (h : IsPushout f g a b)
    (hR : Function.Surjective (Int.castRingHom R)) {ι : Type*} (v : Module.Basis ι ℤ A) :
    Function.Bijective fun c : ι →₀ B ↦ c.sum fun i r ↦ b r * a (v i) := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  let := a.hom.toAlgebra
  let := b.hom.toAlgebra
  let : Algebra R X := (f ≫ a).hom.toAlgebra
  have : IsScalarTower R A X := .of_algebraMap_eq' rfl
  have : IsScalarTower R B X := .of_algebraMap_eq' (by
    change (f ≫ a).hom = (g ≫ b).hom
    rw [h.w])
  have hp : Algebra.IsPushout R A B X := CommRingCat.isPushout_iff_isPushout.mp h
  have hli : LinearIndependent R v := by
    rw [linearIndependent_iff']
    intro t c hc i hi
    choose z hz using fun j ↦ hR (c j)
    have h' : ∑ j ∈ t, z j • v j = 0 := by
      rw [← hc]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← hz j, eq_intCast, Int.cast_smul_eq_zsmul]
    rw [← hz i, linearIndependent_iff'.mp v.linearIndependent t z h' i hi, eq_intCast,
      Int.cast_zero]
  have hsp : (⊤ : Submodule R A) ≤ Submodule.span R (Set.range v) := by
    intro x _
    have := Submodule.span_le_restrictScalars ℤ R (Set.range v)
    exact this (v.span_eq.ge Submodule.mem_top)
  let vX := IsBaseChange.basis (Module.Basis.mk hli hsp) hp.symm.out
  have hvX : ∀ i, vX i = a (v i) := fun i ↦ by
    simp [vX, IsBaseChange.basis_apply]
    rfl
  convert vX.repr.symm.bijective using 1
  ext c
  rw [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply]
  refine Finsupp.sum_congr fun i _ ↦ ?_
  rw [hvX, Algebra.smul_def]
  rfl

end CommRingCat
