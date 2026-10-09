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

lemma monomialToNat_eq_prod (a : n → ℤ) :
    monomialToNat R a = ∏ i, X i ^ (a i).toNat := by
  rw [monomialToNat, monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  rfl

lemma monomialToNat_mem_iff {P : Ideal (MvPolynomial n R)} [P.IsPrime] (a : n → ℤ) :
    monomialToNat R a ∈ P ↔ ∃ i, 0 < a i ∧ X i ∈ P := by
  rw [monomialToNat_eq_prod, Ideal.IsPrime.prod_mem_iff]
  refine ⟨fun ⟨i, _, hi⟩ ↦ ⟨i, ?_, ?_⟩, fun ⟨i, hi, hX⟩ ↦ ⟨i, Finset.mem_univ _, ?_⟩⟩
  · by_contra h
    rw [Int.toNat_of_nonpos (not_lt.1 h), pow_zero, ← Ideal.eq_top_iff_one] at hi
    exact Ideal.IsPrime.ne_top ‹_› hi
  · exact Ideal.IsPrime.mem_of_pow_mem ‹_› _ hi
  · exact Ideal.pow_mem_of_mem _ hX _ (by omega)

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
def negExponentSum (e : n → ℤ) : ℕ := ∑ i, (-e i).toNat

variable {s m}

omit [Fintype n] in
lemma add_nsmul_indicator_nonneg {e : n → ℤ} (he : ∀ i ∉ s, 0 ≤ e i) {N : ℕ}
    (hN : ∀ i, -e i ≤ N) : 0 ≤ e + N • s.indicator (1 : n → ℤ) := by
  intro i
  by_cases hi : i ∈ s
  · simp [Set.indicator_of_mem hi]
    linarith [hN i]
  · simp [Set.indicator_of_notMem hi, he i hi]

lemma neg_le_negExponentSum (e : n → ℤ) (i : n) : -e i ≤ negExponentSum e := by
  have h : (-e i).toNat ≤ negExponentSum e :=
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
  Away.mk _ (monomialToNat_indicator_mem R s) (negExponentSum e.1)
    (monomialToNat R (e.1 + negExponentSum e.1 • s.indicator 1))
    (monomialToNat_add_nsmul_indicator_mem e.2 (neg_le_negExponentSum e.1))

/-- `awayMonomial` may be computed with any large enough power of the denominator. -/
lemma awayMonomial_eq (e : laurentExponents s 0) {N : ℕ} (hN : ∀ i, -e.1 i ≤ N) :
    Away.mk _ (monomialToNat_indicator_mem R s) N (monomialToNat R (e.1 + N • s.indicator 1))
      (monomialToNat_add_nsmul_indicator_mem e.2 hN) = awayMonomial R s e := by
  have h0 := indicator_one_nonneg s
  refine Away.mk_eq_mk_of_mul_pow_eq (𝒜 := homogeneousSubmodule n R)
    (monomialToNat_indicator_mem R s) _ _ ?_
  rw [monomialToNat_pow h0, monomialToNat_pow h0,
    monomialToNat_mul (add_nsmul_indicator_nonneg e.2.2 hN) (nsmul_nonneg h0 _),
    monomialToNat_mul (add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1))
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
  set N := ∑ e ∈ t, negExponentSum e.1
  have hN : ∀ e ∈ t, ∀ i, -e.1 i ≤ N := fun e he i ↦ (neg_le_negExponentSum e.1 i).trans
    (Nat.cast_le.2 (Finset.single_le_sum (f := fun e : laurentExponents s 0 ↦ negExponentSum e.1)
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

namespace AlgebraicGeometry.Proj

open ProjectiveSpectrum.Twist HomogeneousLocalization

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜] {m : ℤ}

/-- Sections of `𝒪(m)` restrict pointwise. -/
lemma twist_presheaf_map_apply {U V : (Proj 𝒜).Opens} (h : V ≤ U) (s : Γ(twist 𝒜 m, U))
    (x : V) : ((twist 𝒜 m).presheaf.map (homOfLE h).op s).1 x = s.1 ⟨x.1, h x.2⟩ :=
  rfl

/-- Sections of the structure sheaf act on sections of `𝒪(m)` by pointwise multiplication. -/
lemma coe_twist_smul_apply {U : (Proj 𝒜).Opens} (r : Γ(Proj 𝒜, U)) (s : Γ(twist 𝒜 m, U))
    (x : U) : ((r • s).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      (r.1 x).val * (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) :=
  rfl

/-- **A section of `𝒪(m)` with a pointwise inverse is a free generator**: if `ε` is a section of
`𝒪(m)` over `U` and `ε'` a section of `𝒪(-m)` over `U` with `ε ε' = 1` at every point, then every
section of `𝒪(m)` over an open `V ⊆ U` is uniquely `r • ε|_V`. -/
lemma isFreeGenerator_twist_of_mul_eq_one {U : (Proj 𝒜).Opens} (ε : Γ(twist 𝒜 m, U))
    (ε' : Γ(twist 𝒜 (-m), U))
    (h : ∀ x : U, (ε.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * ε'.1 x = 1) :
    Scheme.Modules.IsFreeGenerator ε := by
  intro V hV
  constructor
  · intro r r' hrr
    refine Subtype.ext (funext fun x ↦ val_injective _ ?_)
    have hx := congrArg (fun s : Γ(twist 𝒜 m, V) ↦
      (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)) hrr
    dsimp only at hx
    rw [coe_twist_smul_apply, coe_twist_smul_apply, twist_presheaf_map_apply] at hx
    have hx' := congrArg (· * (ε'.1 ⟨x.1, hV x.2⟩ :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)) hx
    dsimp only at hx'
    rwa [mul_assoc, mul_assoc, h, mul_one, mul_one] at hx'
  · intro t
    let ε'V := (twist 𝒜 (-m)).presheaf.map (homOfLE hV).op ε'
    refine ⟨sectionsZeroInv ⟨fun x ↦ ⟨t.1 x * ε'V.1 x, add_neg_cancel m ▸
      mul_mem_degreePart (t.1 x).2 (ε'V.1 x).2⟩, isLocallyFraction_mul (add_neg_cancel m) t.2
        ε'V.2⟩, ?_⟩
    refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
    rw [coe_twist_smul_apply, twist_presheaf_map_apply]
    have := zeroEquiv_sectionsZeroInv (U := Opposite.op V) ⟨fun x ↦ ⟨t.1 x * ε'V.1 x, add_neg_cancel m ▸
      mul_mem_degreePart (t.1 x).2 (ε'V.1 x).2⟩, isLocallyFraction_mul (add_neg_cancel m) t.2
        ε'V.2⟩ x
    have hv := congrArg Subtype.val this
    rw [degreePart.coe_zeroEquiv_apply] at hv
    rw [hv]
    change (t.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
      (ε'.1 ⟨x.1, hV x.2⟩ : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
      (ε.1 ⟨x.1, hV x.2⟩ : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = _
    have hx := h ⟨x.1, hV x.2⟩
    rw [mul_comm] at hx
    rw [mul_assoc, hx, mul_one]

section Monomial

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : Type u} [Fintype n] {R : Type u} [CommRing R] {s : Set n}

/-- A point lies in `D₊(∏_{i ∈ s} Xᵢ)` if and only if it lies in every `D₊(Xᵢ)`, `i ∈ s`. -/
lemma mem_basicOpen_monomialToNat_indicator {x : Proj (homogeneousSubmodule n R)} :
    x ∈ Proj.basicOpen _ (monomialToNat R (s.indicator 1)) ↔
      ∀ i ∈ s, x ∈ Proj.basicOpen (homogeneousSubmodule n R) (X i) := by
  simp only [Proj.mem_basicOpen]
  change monomialToNat R (s.indicator 1) ∉ x.asHomogeneousIdeal.toIdeal ↔
    ∀ i ∈ s, X i ∉ x.asHomogeneousIdeal.toIdeal
  rw [monomialToNat_mem_iff]
  constructor
  · intro h i hi hX
    exact h ⟨i, by simp [Set.indicator_of_mem hi], hX⟩
  · rintro h ⟨i, hi, hX⟩
    by_cases his : i ∈ s
    · exact h i his hX
    · simp [Set.indicator_of_notMem his] at hi

lemma basicOpen_monomialToNat_indicator_mono {s t : Set n} (h : t ⊆ s) :
    Proj.basicOpen (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1)) ≤
      Proj.basicOpen _ (monomialToNat R (t.indicator 1)) := fun _ hx ↦
  mem_basicOpen_monomialToNat_indicator.2 fun i hi ↦
    mem_basicOpen_monomialToNat_indicator.1 hx i (h hi)

/-- Two fractions of monomials agree in a localization as soon as their exponents do. -/
lemma mk_monomialToNat_eq_mk {M : Submonoid (MvPolynomial n R)} {a b a' b' : n → ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b') (h : a + b' = a' + b)
    (hbM : monomialToNat R b ∈ M) (hbM' : monomialToNat R b' ∈ M) :
    Localization.mk (monomialToNat R a) ⟨_, hbM⟩ =
      Localization.mk (monomialToNat R a') ⟨_, hbM'⟩ := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  rw [monomialToNat_mul hb' ha, monomialToNat_mul hb ha', add_comm b', h, add_comm]

omit [Fintype n] in
lemma cast_sum_toNat {a : n → ℤ} (ha : 0 ≤ a) (t : Finset n) :
    ((∑ i ∈ t, (a i).toNat : ℕ) : ℤ) = ∑ i ∈ t, a i := by
  push_cast
  exact Finset.sum_congr rfl fun i _ ↦ Int.toNat_of_nonneg (ha i)

variable (R m) in
/-- **The section `xᵃ / xᵇ` of `𝒪(m)`** over an open `U` of `Proj R[Xᵢ]` on which `xᵇ` does not
vanish, for nonnegative exponent vectors `a`, `b` with `∑ aᵢ = ∑ bᵢ + m`. -/
noncomputable def twistMonomialFraction {a b : n → ℤ} (h : ∑ i, a i = ∑ i, b i + m) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (U : (Proj (homogeneousSubmodule n R)).Opens)
    (hU : ∀ x ∈ U, monomialToNat R b ∉ x.asHomogeneousIdeal) :
    Γ(twist (homogeneousSubmodule n R) m, U) :=
  ⟨fun x ↦ degreePart.mk ⟨monomialToNat R a, monomialToNat_mem a⟩
    ⟨monomialToNat R b, monomialToNat_mem b⟩ (hU x.1 x.2) (by
      rw [cast_sum_toNat ha, cast_sum_toNat hb, h]),
    isLocallyFraction_mk (by rw [cast_sum_toNat ha, cast_sum_toNat hb, h]) _ _
      fun x ↦ hU x.1 x.2⟩

lemma coe_twistMonomialFraction_apply {a b : n → ℤ} (h : ∑ i, a i = ∑ i, b i + m) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (U : (Proj (homogeneousSubmodule n R)).Opens)
    (hU : ∀ x ∈ U, monomialToNat R b ∉ x.asHomogeneousIdeal) (x : U) :
    ((twistMonomialFraction (R := R) (m := m) h ha hb U hU).1 x :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      Localization.mk (monomialToNat R a) ⟨monomialToNat R b, hU x.1 x.2⟩ :=
  rfl

lemma monomialToNat_nsmul_indicator_notMem {x : Proj (homogeneousSubmodule n R)}
    (hx : x ∈ Proj.basicOpen _ (monomialToNat R (s.indicator 1))) (N : ℕ) :
    monomialToNat R (N • s.indicator (1 : n → ℤ)) ∉ x.asHomogeneousIdeal := by
  rw [← monomialToNat_pow (indicator_one_nonneg s)]
  exact fun h ↦ hx (x.isPrime.mem_of_pow_mem N h)

lemma sum_add_nsmul_indicator_eq {e : n → ℤ} (he : ∑ i, e i = m) (N : ℕ) :
    ∑ i, (e + N • s.indicator (1 : n → ℤ)) i = ∑ i, (N • s.indicator (1 : n → ℤ)) i + m := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, he]
  ring

variable (R s) in
/-- **The Laurent monomial `xᵉ` as a section of `𝒪(m)`** over `D₊(∏_{i ∈ s} Xᵢ)`, for an
exponent vector `e` with `∑ eᵢ = m` and `eᵢ ≥ 0` for `i ∉ s`. -/
noncomputable def twistMonomial (e : laurentExponents s m) :
    Γ(twist (homogeneousSubmodule n R) m,
      Proj.basicOpen _ (monomialToNat R (s.indicator 1))) :=
  twistMonomialFraction (R := R) (m := m) (sum_add_nsmul_indicator_eq e.2.1 (negExponentSum e.1))
    (add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1))
    (nsmul_nonneg (indicator_one_nonneg s) _) _
    fun _ hx ↦ monomialToNat_nsmul_indicator_notMem hx _

lemma coe_twistMonomial_apply (e : laurentExponents s m)
    (x : Proj.basicOpen (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1))) :
    ((twistMonomial R s e).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      Localization.mk (monomialToNat R (e.1 + negExponentSum e.1 • s.indicator 1))
        ⟨monomialToNat R (negExponentSum e.1 • s.indicator 1),
          monomialToNat_nsmul_indicator_notMem x.2 _⟩ :=
  rfl

/-- The Laurent monomial `xᵉ` on `D₊(∏_{i ∈ t} Xᵢ)` restricts to the Laurent monomial `xᵉ` on
the smaller open `D₊(∏_{i ∈ s} Xᵢ)`, for `t ⊆ s`. -/
lemma twist_presheaf_map_twistMonomial {t : Set n} (hts : t ⊆ s) (e : laurentExponents t m) :
    (twist (homogeneousSubmodule n R) m).presheaf.map
        (homOfLE (basicOpen_monomialToNat_indicator_mono (R := R) hts)).op
        (twistMonomial R t e) =
      twistMonomial R s ⟨e.1, e.2.1, fun i hi ↦ e.2.2 i fun h ↦ hi (hts h)⟩ := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  rw [twist_presheaf_map_apply, coe_twistMonomial_apply, coe_twistMonomial_apply]
  have h0 := indicator_one_nonneg s
  have h0' := indicator_one_nonneg t
  refine mk_monomialToNat_eq_mk (add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1))
    (nsmul_nonneg h0' _) (add_nsmul_indicator_nonneg (fun i hi ↦ e.2.2 i fun h ↦ hi (hts h))
      (neg_le_negExponentSum e.1)) (nsmul_nonneg h0 _) ?_ _ _
  abel

/-- A fraction of monomials in a localization only depends on the difference of the exponents. -/
lemma mk_eq_mk_of_monomialToNat {M : Submonoid (MvPolynomial n R)} {x x' : MvPolynomial n R}
    {d d' : M} {a b a' b' : n → ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b')
    (hx : x = monomialToNat R a) (hd : (d : MvPolynomial n R) = monomialToNat R b)
    (hx' : x' = monomialToNat R a') (hd' : (d' : MvPolynomial n R) = monomialToNat R b')
    (h : a + b' = a' + b) : Localization.mk x d = Localization.mk x' d' := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  rw [hx, hd, hx', hd', monomialToNat_mul hb' ha, monomialToNat_mul hb ha', add_comm b', h,
    add_comm]

lemma monomialToNat_zero : monomialToNat R (0 : n → ℤ) = 1 := by
  rw [monomialToNat]
  have : (Finsupp.equivFunOnFinite.symm fun i ↦ ((0 : n → ℤ) i).toNat) = 0 := by
    ext i
    simp
  rw [this, ← C_1, C_apply]

variable (s m) in
open Classical in
/-- The exponent vector `m eᵢ` of the monomial `Xᵢ ^ m`, for `i ∈ s`. -/
noncomputable def singleExponent {i : n} (hi : i ∈ s) : laurentExponents s m :=
  ⟨Pi.single i m, by simp, fun j hj ↦ by
    rw [Pi.single_apply, if_neg fun h : j = i ↦ hj (h ▸ hi)]⟩

/-- `xᵢ ^ m` is a free generator of `𝒪(m)` on `D₊(∏_{j ∈ s} Xⱼ)`, for `i ∈ s`. -/
lemma isFreeGenerator_twistMonomial_singleExponent {i : n} (hi : i ∈ s) :
    Scheme.Modules.IsFreeGenerator (twistMonomial R s (singleExponent (s := s) (m := m) hi)) := by
  refine isFreeGenerator_twist_of_mul_eq_one _ (twistMonomial R s (singleExponent (s := s) (m := -m) hi))
    fun x ↦ ?_
  rw [coe_twistMonomial_apply, coe_twistMonomial_apply, Localization.mk_mul,
    ← Localization.mk_one]
  have h0 := indicator_one_nonneg s
  have ha := add_nsmul_indicator_nonneg (singleExponent (s := s) (m := m) hi).2.2
    (neg_le_negExponentSum (singleExponent (s := s) (m := m) hi).1)
  have ha' := add_nsmul_indicator_nonneg (singleExponent (s := s) (m := -m) hi).2.2
    (neg_le_negExponentSum (singleExponent (s := s) (m := -m) hi).1)
  have hN := nsmul_nonneg h0 (negExponentSum (singleExponent (s := s) (m := m) hi).1)
  have hN' := nsmul_nonneg h0 (negExponentSum (singleExponent (s := s) (m := -m) hi).1)
  refine mk_eq_mk_of_monomialToNat (add_nonneg ha ha') (add_nonneg hN hN') le_rfl le_rfl
    (monomialToNat_mul ha ha') ?_ monomialToNat_zero.symm monomialToNat_zero.symm ?_
  · exact monomialToNat_mul hN hN'
  · ext j
    simp only [singleExponent, Pi.add_apply, Pi.zero_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> ring

/-- The value at a point of the function `xᵉ` on `D₊(∏_{i ∈ s} Xᵢ)`. -/
lemma val_awayToSection_awayMonomial_apply (e : laurentExponents s 0)
    (x : Proj.basicOpen (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1))) :
    ((Proj.awayToSection _ _ (awayMonomial R s e)).1 x).val =
      Localization.mk (monomialToNat R (e.1 + negExponentSum e.1 • s.indicator 1))
        ⟨monomialToNat R (negExponentSum e.1 • s.indicator 1),
          monomialToNat_nsmul_indicator_notMem x.2 _⟩ := by
  have := ProjectiveSpectrum.Proj.awayToSection_apply (homogeneousSubmodule n R)
    (monomialToNat R (s.indicator 1)) (awayMonomial R s e) x
  erw [this]
  rw [awayMonomial, Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    RingHom.id_apply, ← Localization.mk_eq_mk']
  have h0 := indicator_one_nonneg s
  have ha := add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1)
  exact mk_eq_mk_of_monomialToNat ha (nsmul_nonneg h0 _) ha (nsmul_nonneg h0 _) rfl
    (monomialToNat_pow h0 _) rfl rfl rfl

open Classical in
variable (m) in
/-- The exponent vector `e - m eᵢ` of `xᵉ / xᵢ ^ m`, for `i ∈ s`. -/
noncomputable def shiftExponent {i : n} (hi : i ∈ s) (e : laurentExponents s m) :
    laurentExponents s 0 :=
  ⟨e.1 - Pi.single i m, by simp [Finset.sum_sub_distrib, e.2.1], fun j hj ↦ by
    rw [Pi.sub_apply, Pi.single_apply, if_neg fun h : j = i ↦ hj (h ▸ hi), sub_zero]
    exact e.2.2 j hj⟩

/-- **`xᵉ = (xᵉ / xᵢ ^ m) xᵢ ^ m`** in `𝒪(m)` over `D₊(∏_{j ∈ s} Xⱼ)`, for `i ∈ s`. -/
lemma twistMonomial_eq_smul {i : n} (hi : i ∈ s) (e : laurentExponents s m) :
    twistMonomial R s e = Proj.awayToSection _ _ (awayMonomial R s (shiftExponent m hi e)) •
      twistMonomial R s (singleExponent (s := s) (m := m) hi) := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change ((twistMonomial R s e).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = _
  rw [coe_twist_smul_apply, coe_twistMonomial_apply, coe_twistMonomial_apply,
    val_awayToSection_awayMonomial_apply, Localization.mk_mul]
  have h0 := indicator_one_nonneg s
  have ha := add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1)
  have hb := add_nsmul_indicator_nonneg (shiftExponent m hi e).2.2
    (neg_le_negExponentSum (shiftExponent m hi e).1)
  have hc := add_nsmul_indicator_nonneg (singleExponent (s := s) (m := m) hi).2.2
    (neg_le_negExponentSum (singleExponent (s := s) (m := m) hi).1)
  have hN := nsmul_nonneg h0 (negExponentSum (shiftExponent m hi e).1)
  have hN' := nsmul_nonneg h0 (negExponentSum (singleExponent (s := s) (m := m) hi).1)
  refine mk_eq_mk_of_monomialToNat ha (nsmul_nonneg h0 _) (add_nonneg hb hc)
    (add_nonneg hN hN') rfl rfl (monomialToNat_mul hb hc) (monomialToNat_mul hN hN') ?_
  ext j
  simp only [shiftExponent, singleExponent, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.single_apply]
  split_ifs <;> ring

end Monomial

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjectiveSpace

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u) (S : Scheme.{u})

/-- The preimage in `ℙ(n; S)` of an open `W` of the integral model `ℙⁿ_ℤ` is the base change of
`W` along `S ⟶ Spec ℤ`. -/
lemma isPullback_preimage (W : (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)).Opens) :
    IsPullback ((toProjInt n S).resLE W (toProjInt n S ⁻¹ᵁ W) le_rfl)
      ((toProjInt n S ⁻¹ᵁ W).ι ≫ ℙ(n; S) ↘ S) (terminal.from W.toScheme) (terminal.from S) := by
  have h := (isPullback_morphismRestrict (toProjInt n S) W).paste_vert
    (isPullback_over_toProjInt n S).flip
  have hr : (toProjInt n S).resLE W (toProjInt n S ⁻¹ᵁ W) le_rfl = toProjInt n S ∣_ W :=
    Scheme.Hom.resLE_eq_morphismRestrict ..
  exact h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by rw [Iso.refl_hom, Category.comp_id]; exact hr.symm.trans (Category.id_comp _).symm)
    (by rw [Iso.refl_hom, Category.comp_id]; exact (Category.id_comp _).symm)
    (terminal.hom_ext _ _) (terminal.hom_ext _ _)

/-- The ring of global functions on the terminal scheme `Spec ℤ` is a quotient of `ℤ`. -/
lemma surjective_intCastRingHom_Γ_terminal :
    Function.Surjective (Int.castRingHom Γ(⊤_ Scheme.{u}, ⊤)) := by
  let e : Γ(⊤_ Scheme.{u}, ⊤) ≅ CommRingCat.of (ULift.{u} ℤ) :=
    Scheme.Γ.mapIso (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).op ≪≫
      Scheme.ΓSpecIso _
  intro y
  refine ⟨(e.hom y).down, e.commRingCatIsoToRingEquiv.injective ?_⟩
  change e.hom _ = e.hom y
  rw [eq_intCast, map_intCast]
  rfl

variable {n} [Fintype n]

/-- The monomial basis of `ℤ[Xᵢ]_{(∏_{i ∈ s} Xᵢ)}`, as a `ℤ`-basis. -/
noncomputable def awayMonomialBasisInt (s : Set n) :
    Module.Basis (laurentExponents s 0) ℤ
      (HomogeneousLocalization.Away (homogeneousSubmodule n (ULift.{u} ℤ))
        (monomialToNat (ULift.{u} ℤ) (s.indicator 1))) :=
  (awayMonomialBasis (ULift.{u} ℤ) s).mapCoeffs ULift.ringEquiv fun c x ↦ by
    conv_rhs => rw [show c = ((c.down : ℤ) : ULift.{u} ℤ) from ULift.ext _ _ (by simp)]
    rw [Int.cast_smul_eq_zsmul]
    rfl

@[simp]
lemma awayMonomialBasisInt_apply (s : Set n) (e : laurentExponents s 0) :
    awayMonomialBasisInt s e = awayMonomial (ULift.{u} ℤ) s e := by
  simp [awayMonomialBasisInt]

lemma indicatorDegree_pos {s : Set n} (hs : s.Nonempty) : 0 < indicatorDegree s := by
  obtain ⟨i, hi⟩ := hs
  have : 0 < (s.indicator (1 : n → ℤ) i).toNat := by simp [Set.indicator_of_mem hi]
  exact this.trans_le (Finset.single_le_sum (f := fun j ↦ (s.indicator (1 : n → ℤ) j).toNat)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i))

variable (n) in
/-- The open `D₊(∏_{i ∈ s} Xᵢ)` of the integral model `ℙⁿ_ℤ`. -/
noncomputable abbrev basicOpenInt (s : Set n) :
    (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)).Opens :=
  Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (monomialToNat _ (s.indicator 1))

/-- **The functions on `⋂_{i ∈ s} D₊(xᵢ) ⊆ ℙ(n; Spec k)`**: every function is uniquely a finite
`k`-linear combination of the Laurent monomials `xᵉ`, `∑ eᵢ = 0`, `eᵢ ≥ 0` for `i ∉ s`. This is
the base change to `k` of the monomial basis of `ℤ[Xᵢ]_{(∏_{i ∈ s} Xᵢ)}`. -/
theorem bijective_sum_awayMonomial (k : Type u) [CommRing k] {s : Set n} (hs : s.Nonempty) :
    Function.Bijective fun c : laurentExponents s 0 →₀ k ↦ c.sum fun e r ↦
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appTop ≫
        ℙ(n; Spec (.of k)).presheaf.map (homOfLE le_top).op) r *
      (Proj.awayToSection _ _ ≫ (toProjInt n (Spec (.of k))).appLE (basicOpenInt n s)
        (toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n s) le_rfl)
        (awayMonomial (ULift.{u} ℤ) s e) := by
  have hdeg := indicatorDegree_pos hs
  have hf := monomialToNat_indicator_mem (ULift.{u} ℤ) s
  have hW : IsAffineOpen (basicOpenInt n s) := Proj.isAffineOpen_basicOpen _ _ hf hdeg
  have : IsAffine (basicOpenInt n s).toScheme := hW
  have hpo := isPushout_appTop_of_isPullback (isPullback_preimage n (Spec (.of k))
    (basicOpenInt n s))
  have hpo' := hpo.of_iso (Iso.refl _)
    ((basicOpenInt n s).topIso ≪≫ (Proj.basicOpenIsoAway _ _ hf hdeg).symm)
    (Scheme.ΓSpecIso (.of k)) (toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n s).topIso
    (f' := Scheme.Hom.appTop (terminal.from (basicOpenInt n s).toScheme) ≫ (basicOpenInt n s).topIso.hom ≫
      (Proj.basicOpenIsoAway _ _ hf hdeg).inv)
    (g' := Scheme.Hom.appTop (terminal.from (Spec (.of k))) ≫ (Scheme.ΓSpecIso (.of k)).hom)
    (inl' := Proj.awayToSection _ _ ≫ (toProjInt n (Spec (.of k))).appLE (basicOpenInt n s)
        (toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n s) le_rfl)
    (inr' := (Scheme.ΓSpecIso (.of k)).inv ≫ (ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appTop ≫
        ℙ(n; Spec (.of k)).presheaf.map (homOfLE le_top).op)
    (by simp) (by simp) ?_ ?_
  · convert CommRingCat.IsPushout.bijective_sum_mul hpo' surjective_intCastRingHom_Γ_terminal
      (awayMonomialBasisInt s) using 1
    ext c
    simp
  · rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← Proj.basicOpenIsoAway_hom _ _ hf hdeg, Category.assoc]
    erw [Iso.inv_hom_id_assoc]
  · rw [Iso.hom_inv_id_assoc, Scheme.Hom.comp_appTop, Category.assoc,
      Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
    rfl

section Twist

open Scheme.Modules

variable {m : ℤ}

/-- **The Laurent monomial `xᵉ` as a section of `𝒪(m)`** over `⋂_{i ∈ s} D₊(xᵢ) ⊆ ℙ(n; S)`, for
an exponent vector `e` with `∑ eᵢ = m` and `eᵢ ≥ 0` for `i ∉ s`: the pullback of the section
`xᵉ` of `𝒪(m)` on the integral model. -/
noncomputable def twistMonomialSection (s : Set n) (e : laurentExponents s m) :
    Γ(twist n S m, toProjInt n S ⁻¹ᵁ basicOpenInt n s) :=
  pullbackSection (toProjInt n S) (Proj.twistMonomial (ULift.{u} ℤ) s e)

variable {S}

lemma twist_presheaf_map_twistMonomialSection {s t : Set n} (hts : t ⊆ s)
    (e : laurentExponents t m) :
    (twist n S m).presheaf.map (homOfLE ((toProjInt n S).preimage_mono
        (Proj.basicOpen_monomialToNat_indicator_mono (R := ULift.{u} ℤ) hts))).op
        (twistMonomialSection S t e) =
      twistMonomialSection S s ⟨e.1, e.2.1, fun i hi ↦ e.2.2 i fun h ↦ hi (hts h)⟩ := by
  have h := pullbackSection_map (toProjInt n S)
    (Proj.basicOpen_monomialToNat_indicator_mono (R := ULift.{u} ℤ) hts)
    (Proj.twistMonomial (ULift.{u} ℤ) t e)
  rw [Proj.twist_presheaf_map_twistMonomial hts] at h
  exact h.symm

lemma twistMonomialSection_eq_smul {s : Set n} {i : n} (hi : i ∈ s) (e : laurentExponents s m) :
    twistMonomialSection S s e =
      (Proj.awayToSection _ _ ≫ (toProjInt n S).appLE (basicOpenInt n s)
        (toProjInt n S ⁻¹ᵁ basicOpenInt n s) le_rfl)
        (awayMonomial (ULift.{u} ℤ) s (Proj.shiftExponent m hi e)) •
        twistMonomialSection S s (Proj.singleExponent (s := s) (m := m) hi) := by
  rw [twistMonomialSection, Proj.twistMonomial_eq_smul hi e, pullbackSection_smul,
    Scheme.Hom.appLE_eq_app]
  rfl

lemma isFreeGenerator_twistMonomialSection_singleExponent {s : Set n} {i : n} (hi : i ∈ s) :
    IsFreeGenerator (twistMonomialSection S s (Proj.singleExponent (s := s) (m := m) hi)) :=
  (Proj.isFreeGenerator_twistMonomial_singleExponent hi).pullback_unit_app (toProjInt n S)

open Classical in
variable (m) in
/-- Shifting exponent vectors by `m eᵢ`, for `i ∈ s`, identifies the Laurent monomials of
degree `m` regular on `⋂_{j ∈ s} D₊(xⱼ)` with those of degree `0`. -/
noncomputable def shiftExponentEquiv {s : Set n} {i : n} (hi : i ∈ s) :
    laurentExponents s m ≃ laurentExponents s 0 where
  toFun := Proj.shiftExponent m hi
  invFun e := ⟨e.1 + Pi.single i m, by simp [Finset.sum_add_distrib, e.2.1], fun j hj ↦ by
    rw [Pi.add_apply, Pi.single_apply, if_neg fun h : j = i ↦ hj (h ▸ hi), add_zero]
    exact e.2.2 j hj⟩
  left_inv e := Subtype.ext (by simp [Proj.shiftExponent])
  right_inv e := Subtype.ext (by simp [Proj.shiftExponent])

/-- **The sections of `𝒪(m)` over `⋂_{i ∈ s} D₊(xᵢ) ⊆ ℙ(n; Spec k)`** for nonempty `s`: every
section is uniquely a finite `k`-linear combination of the Laurent monomials `xᵉ` with
`∑ eᵢ = m` and `eᵢ ≥ 0` for `i ∉ s`. -/
theorem bijective_sum_twistMonomialSection (k : Type u) [CommRing k] {s : Set n}
    (hs : s.Nonempty) (m : ℤ) :
    Function.Bijective fun c : laurentExponents s m →₀ k ↦ c.sum fun e r ↦
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appTop ≫
        ℙ(n; Spec (.of k)).presheaf.map
          (homOfLE (le_top : toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n s ≤ ⊤)).op) r •
        twistMonomialSection (Spec (.of k)) s e := by
  obtain ⟨i, hi⟩ := hs
  have hfun : (fun c : laurentExponents s m →₀ k ↦ c.sum fun e r ↦
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appTop ≫
        ℙ(n; Spec (.of k)).presheaf.map
          (homOfLE (le_top : toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n s ≤ ⊤)).op) r •
        twistMonomialSection (Spec (.of k)) s e) =
      (fun r ↦ r • twistMonomialSection (Spec (.of k)) s
        (Proj.singleExponent (s := s) (m := m) hi)) ∘
      (fun c : laurentExponents s 0 →₀ k ↦ c.sum fun e r ↦
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appTop ≫
          ℙ(n; Spec (.of k)).presheaf.map
          (homOfLE (le_top : toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n s ≤ ⊤)).op) r *
        (Proj.awayToSection _ _ ≫ (toProjInt n (Spec (.of k))).appLE (basicOpenInt n s)
          (toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n s) le_rfl)
          (awayMonomial (ULift.{u} ℤ) s e)) ∘
      Finsupp.equivMapDomain (shiftExponentEquiv m hi) := by
    funext c
    simp only [Function.comp_apply, Finsupp.sum_equivMapDomain]
    rw [Finsupp.sum, Finsupp.sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [twistMonomialSection_eq_smul hi e, mul_smul]
    rfl
  rw [hfun]
  exact (isFreeGenerator_twistMonomialSection_singleExponent hi).bijective.comp
    ((bijective_sum_awayMonomial k ⟨i, hi⟩).comp
      (Finsupp.domCongr (M := k) (shiftExponentEquiv m hi)).bijective)

end Twist

end AlgebraicGeometry.ProjectiveSpace
