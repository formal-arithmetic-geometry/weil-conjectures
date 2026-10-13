/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.OrzechProperty
public import Mathlib.LinearAlgebra.Projection

/-!
# Infinitesimal neighbourhoods of a section of a smooth algebra

Let `A` be a local ring and `R` a formally smooth `A`-algebra with an `A`-algebra section
`σ : R → A` (geometrically: a section of a smooth morphism, at a point) whose kernel `I` is
finitely generated. Then `I/I²` is a free `A`-module of finite rank `d`, and for every `n` the
`n`-th infinitesimal neighbourhood `R / Iⁿ` is isomorphic to the truncated polynomial ring
`A[X₁, …, X_d] / (X)ⁿ`; in particular it is a free, hence flat, `A`-module
(`Algebra.FormallySmooth.flat_quotient_pow_ker`). This is the algebraic content of
[Stacks 05D5] (the completion of a smooth algebra along a section is a power series ring).
-/

@[expose] public section

open MvPolynomial

namespace Algebra.FormallySmooth

section Nilpotent

variable {R' : Type*} [CommRing R']

/-- If `J ⊆ R'` is a nilpotent ideal generated modulo `J²` by elements of a subring `S`, and
`R' = S + J`, then `S = R'`. -/
lemma mem_of_isNilpotent {S : Subring R'} {J : Ideal R'} {n : ℕ} (hJn : J ^ n = ⊥)
    {ι : Type*} [Fintype ι] (y : ι → R') (hyS : ∀ i, y i ∈ S) (hyJ : ∀ i, y i ∈ J)
    (hJ : J ≤ Ideal.span (Set.range y) ⊔ J ^ 2) (hS : ∀ z, ∃ s ∈ S, z - s ∈ J) (z : R') :
    z ∈ S := by
  set J' := Ideal.span (Set.range y)
  have hJ'J : J' ≤ J := Ideal.span_le.2 (Set.range_subset_iff.2 hyJ)
  -- `J = J'`
  have hk : ∀ k, J ≤ J' ⊔ J ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa using le_sup_right
    | succ k ih =>
      calc J ≤ J' ⊔ J ^ 2 := hJ
        _ = J' ⊔ J * J := by rw [pow_two]
        _ ≤ J' ⊔ J * (J' ⊔ J ^ (k + 1)) := sup_le_sup_left (Ideal.mul_mono_right ih) _
        _ ≤ J' ⊔ J ^ (k + 1 + 1) := by
          rw [Ideal.mul_sup]
          refine sup_le le_sup_left (sup_le (le_sup_of_le_left Ideal.mul_le_left) ?_)
          rw [← pow_succ']
  have hJJ' : J = J' := by
    refine le_antisymm ?_ hJ'J
    have := hk n
    rw [pow_succ, hJn, Ideal.bot_mul, sup_bot_eq] at this
    exact this
  -- `J'^k ⊆ (S ∩ J'^k) + J'^(k+1)`
  have hstep : ∀ k, ∀ w ∈ J' ^ k, ∃ s ∈ S, s ∈ J' ^ k ∧ w - s ∈ J' ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro w _
      obtain ⟨s, hs, hws⟩ := hS w
      exact ⟨s, hs, by simp, by simpa [← hJJ'] using hws⟩
    | succ k ih =>
      intro w hw
      rw [pow_succ'] at hw
      induction hw using Submodule.mul_induction_on with
      | mem_mul_mem x hx w hw =>
        obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R').1 hx
        -- `x * w = ∑ yᵢ (rᵢ w)`
        have : ∀ i, ∃ s ∈ S, s ∈ J' ^ (k + 1) ∧ y i * (r i * w) - s ∈ J' ^ (k + 1 + 1) := by
          intro i
          obtain ⟨s, hs, hsk, hws⟩ := ih (r i * w) (Ideal.mul_mem_left _ _ hw)
          refine ⟨y i * s, S.mul_mem (hyS i) hs, ?_, ?_⟩
          · rw [pow_succ']
            exact Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) hsk
          · rw [← mul_sub, pow_succ' _ (k + 1)]
            exact Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) hws
        choose s hs hsk hws using this
        refine ⟨∑ i, s i, Subring.sum_mem _ fun i _ ↦ hs i, Ideal.sum_mem _ fun i _ ↦ hsk i, ?_⟩
        have : (∑ i, r i • y i) * w = ∑ i, y i * (r i * w) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul]; ring
        rw [this, ← Finset.sum_sub_distrib]
        exact Ideal.sum_mem _ fun i _ ↦ hws i
      | add w₁ w₂ _ _ h₁ h₂ =>
        obtain ⟨s₁, hs₁, hsk₁, hw₁⟩ := h₁
        obtain ⟨s₂, hs₂, hsk₂, hw₂⟩ := h₂
        refine ⟨s₁ + s₂, S.add_mem hs₁ hs₂, add_mem hsk₁ hsk₂, ?_⟩
        rw [add_sub_add_comm]
        exact add_mem hw₁ hw₂
  have happrox : ∀ k, ∃ s ∈ S, z - s ∈ J' ^ k := by
    intro k
    induction k with
    | zero => exact ⟨0, S.zero_mem, by simp⟩
    | succ k ih =>
      obtain ⟨s, hs, hzs⟩ := ih
      obtain ⟨s', hs', -, hzs'⟩ := hstep k _ hzs
      exact ⟨s + s', S.add_mem hs hs', by rw [← sub_sub]; exact hzs'⟩
  obtain ⟨s, hs, hzs⟩ := happrox n
  rw [← hJJ', hJn, Ideal.mem_bot, sub_eq_zero] at hzs
  exact hzs ▸ hs

end Nilpotent
section TruncPoly

variable (A : Type*) [CommRing A]

/-- The truncated polynomial ring `A[X₀, …, X_{d-1}] / (X)ⁿ`. -/
abbrev TruncPoly (d n : ℕ) : Type _ := MvPolynomial (Fin d) A ⧸ idealOfVars (Fin d) A ^ n

/-- The truncated polynomial ring is a free `A`-module of finite rank. -/
lemma free_finite_truncPoly (d n : ℕ) :
    Module.Free A (TruncPoly A d n) ∧ Module.Finite A (TruncPoly A d n) := by
  rcases n with _ | m
  · have : Subsingleton (TruncPoly A d 0) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    exact ⟨Module.Free.of_subsingleton' _ _, inferInstance⟩
  set p : Submodule A (MvPolynomial (Fin d) A) := (idealOfVars (Fin d) A ^ (m + 1)).restrictScalars A
  set q := restrictTotalDegree (Fin d) A m
  have hp : p = restrictSupport A {x | m + 1 ≤ x.degree} := by
    rw [← restrictScalars_restrictSupportIdeal ((isUpperSet_Ici (m + 1)).preimage
      Finsupp.degree_mono), ← pow_idealOfVars]
    rfl
  have hdeg (x : Fin d →₀ ℕ) : x.degree = x.sum fun _ e ↦ e := rfl
  have hcompl : IsCompl p q := by
    constructor
    · rw [Submodule.disjoint_def]
      intro r hrp hrq
      rw [hp, mem_restrictSupport_iff] at hrp
      rw [restrictTotalDegree, mem_restrictSupport_iff] at hrq
      by_contra hr
      obtain ⟨x, hx⟩ := MvPolynomial.support_nonempty.2 hr
      have h1 : m + 1 ≤ x.degree := hrp hx
      have h2 : (x.sum fun _ e ↦ e) ≤ m := hrq hx
      rw [hdeg] at h1
      omega
    · have hst : {x : Fin d →₀ ℕ | m + 1 ≤ x.degree} ∪ {x | (x.sum fun _ e ↦ e) ≤ m} =
          Set.univ := by
        ext x
        simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
        rw [hdeg]
        omega
      rw [codisjoint_iff, hp, restrictTotalDegree, restrictSupport_eq_span,
        restrictSupport_eq_span, ← Submodule.span_union, ← Set.image_union, hst,
        ← restrictSupport_eq_span, restrictSupport_univ]
  let e : TruncPoly A d (m + 1) ≃ₗ[A] q :=
    (Submodule.Quotient.restrictScalarsEquiv A (idealOfVars (Fin d) A ^ (m + 1))).symm ≪≫ₗ
      Submodule.quotientEquivOfIsCompl p q hcompl
  have : Module.Free A q := .of_basis (basisRestrictSupport A _)
  exact ⟨.of_equiv e.symm, .equiv e.symm⟩

end TruncPoly
section Truncation

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] [Algebra R A]
  [IsScalarTower A R A]

lemma algebraMap_algebraMap_section (a : A) : algebraMap R A (algebraMap A R a) = a := by
  rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

lemma sub_algebraMap_mem_ker (r : R) :
    r - algebraMap A R (algebraMap R A r) ∈ RingHom.ker (algebraMap R A) := by
  rw [RingHom.mem_ker, map_sub, algebraMap_algebraMap_section, sub_self]

variable (A R) in
/-- The conormal module `I/I²` of a section of a formally smooth algebra is projective. -/
theorem projective_cotangent_ker [FormallySmooth A R] :
    Module.Projective A (RingHom.ker (algebraMap R A)).Cotangent := by
  have hf : Function.Surjective (algebraMap R A) := fun a ↦
    ⟨algebraMap A R a, algebraMap_algebraMap_section a⟩
  obtain ⟨l, hl⟩ :=
    (Algebra.FormallySmooth.iff_split_injection (R := A) (P := R) (A := A) hf).1 inferInstance
  exact Module.Projective.of_split
    ((KaehlerDifferential.kerCotangentToTensor A R A).restrictScalars A) (l.restrictScalars A)
    (LinearMap.ext fun x ↦ LinearMap.congr_fun hl x)

lemma smul_cotangent_ker (r : R) (x : (RingHom.ker (algebraMap R A)).Cotangent) :
    r • x = algebraMap R A r • x := by
  set I := RingHom.ker (algebraMap R A)
  calc r • x = (Ideal.Quotient.mk I r) • x := by
        rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    _ = (Ideal.Quotient.mk I (algebraMap A R (algebraMap R A r))) • x := by
        rw [Ideal.Quotient.eq.2 (sub_algebraMap_mem_ker r)]
    _ = algebraMap A R (algebraMap R A r) • x := by
        rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    _ = algebraMap R A r • x := algebraMap_smul R _ x

variable (A R) in
/-- The conormal module `I/I²` of a section is a finite `A`-module if `R` is Noetherian. -/
theorem finite_cotangent_ker [IsNoetherianRing R] :
    Module.Finite A (RingHom.ker (algebraMap R A)).Cotangent := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := (RingHom.ker (algebraMap R A)).Cotangent)
  refine ⟨⟨s, eq_top_iff.2 fun x _ ↦ ?_⟩⟩
  have hx : x ∈ Submodule.span R (s : Set _) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul r y _ hy => rw [smul_cotangent_ker]; exact Submodule.smul_mem _ _ hy

/-- A monomial exponent of degree one is a basis vector. -/
lemma exists_eq_single_of_degree_eq_one {d : ℕ} (y : Fin d →₀ ℕ) (hy : y.degree = 1) :
    ∃ k, y = Finsupp.single k 1 := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.2 hy0
  have hle : ∀ i ∈ y.support, y i ≤ 1 := fun i hi ↦
    hy ▸ Finset.single_le_sum (f := fun i ↦ y i) (fun _ _ ↦ Nat.zero_le _) hi
  have hyk : y k = 1 := le_antisymm (hle k hk) (Nat.one_le_iff_ne_zero.2
    (Finsupp.mem_support_iff.1 hk))
  refine ⟨k, Finsupp.ext fun i ↦ ?_⟩
  by_cases hik : i = k
  · subst hik; simp [hyk]
  · rw [Finsupp.single_eq_of_ne (Ne.symm hik)]
    by_contra hne
    have hi : i ∈ y.support := Finsupp.mem_support_iff.2 hne
    have : y i + y k ≤ y.degree := by
      rw [Finsupp.degree, ← Finset.sum_pair hik]
      exact Finset.sum_le_sum_of_subset (Finset.insert_subset hi (Finset.singleton_subset_iff.2 hk))
    omega

/-- The linear part of a polynomial: `p ≡ p(0) + ∑ ∂ⱼp(0) Xⱼ` modulo `(X)²`. -/
lemma sub_linearPart_mem_pow_two {d : ℕ} (p : MvPolynomial (Fin d) A) :
    p - (C (coeff 0 p) + ∑ j, C (coeff (Finsupp.single j 1) p) * X j) ∈
      idealOfVars (Fin d) A ^ 2 := by
  classical
  rw [mem_pow_idealOfVars_iff']
  intro y hy
  rw [coeff_sub, coeff_add, coeff_sum, coeff_C]
  simp only [coeff_C_mul_X']
  rcases Nat.lt_succ_iff_lt_or_eq.1 hy with h0 | h1
  · have hy0 : y = 0 := by
      rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at h0
      exact h0
    subst hy0
    simp
  · obtain ⟨k, rfl⟩ := exists_eq_single_of_degree_eq_one y h1
    simp [Finsupp.single_eq_zero, Finset.sum_ite_eq', Finsupp.single_left_inj]

/-- The constant term: `p ≡ p(0)` modulo `(X)`. -/
lemma sub_C_coeff_zero_mem {d : ℕ} (p : MvPolynomial (Fin d) A) :
    p - C (coeff 0 p) ∈ idealOfVars (Fin d) A := by
  rw [← pow_one (idealOfVars (Fin d) A), mem_pow_idealOfVars_iff']
  intro y hy
  rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hy
  subst hy
  simp

end Truncation
section Main

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] [Algebra R A]
  [IsScalarTower A R A] [IsLocalRing A] [IsNoetherianRing R] [FormallySmooth A R]

variable (A R) in
/-- **Infinitesimal neighbourhoods of a section of a smooth algebra.** Let `A` be a local ring and
`R` a formally smooth Noetherian `A`-algebra with a section `R → A` of kernel `I`. Then there is
`d` such that `R / Iⁿ ≅ A[X₁, …, X_d] / (X)ⁿ` for all `n ≥ 2`. -/
theorem exists_algEquiv_truncPoly :
    ∃ d : ℕ, ∀ n, 2 ≤ n →
      Nonempty ((R ⧸ RingHom.ker (algebraMap R A) ^ n) ≃ₐ[A] TruncPoly A d n) := by
  classical
  set I := RingHom.ker (algebraMap R A)
  have := projective_cotangent_ker A R
  have := finite_cotangent_ker A R
  have : Module.Free A I.Cotangent := Module.free_of_flat_of_isLocalRing
  set d := Module.finrank A I.Cotangent
  let v := Module.finBasis A I.Cotangent
  choose x hx using fun j ↦ I.toCotangent_surjective (v j)
  have hxI (j : Fin d) : algebraMap R A (x j) = 0 := (x j).2
  -- the decomposition `i ≡ ∑ cⱼ xⱼ` modulo `I²`
  have hdec (i : R) (hi : i ∈ I) :
      i - ∑ j, algebraMap A R (v.repr (I.toCotangent ⟨i, hi⟩) j) * x j ∈ I ^ 2 := by
    set c := v.repr (I.toCotangent ⟨i, hi⟩)
    let y : I := ⟨i, hi⟩ - ∑ j, algebraMap A R (c j) • x j
    have hy : (y : R) = i - ∑ j, algebraMap A R (c j) * x j := by
      simp [y, Submodule.coe_sum, smul_eq_mul]
    rw [← hy, ← I.toCotangent_eq_zero]
    simp only [y, map_sub, map_sum, map_smul, hx, algebraMap_smul]
    rw [sub_eq_zero]
    exact (v.sum_repr _).symm
  -- the map `ψₙ : A[X]/(X)ⁿ → R/Iⁿ`, `Xⱼ ↦ xⱼ`
  let F (n : ℕ) : MvPolynomial (Fin d) A →ₐ[A] R ⧸ I ^ n :=
    aeval fun j ↦ Ideal.Quotient.mk (I ^ n) (x j)
  have hF (n : ℕ) : ∀ p ∈ idealOfVars (Fin d) A ^ n, F n p = 0 := by
    intro p hp
    have h1 : (idealOfVars (Fin d) A).map (F n) ≤ I.map (Ideal.Quotient.mk (I ^ n)) := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      simp only [F, aeval_X]
      exact Ideal.mem_map_of_mem _ (x j).2
    have h2 := Ideal.mem_map_of_mem (F n) hp
    rw [Ideal.map_pow] at h2
    have h3 := Ideal.pow_right_mono h1 n h2
    rwa [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.mem_bot] at h3
  let ψ (n : ℕ) : TruncPoly A d n →ₐ[A] R ⧸ I ^ n := Ideal.Quotient.liftₐ _ (F n) (hF n)
  have hψmk (n : ℕ) (p) : ψ n (Ideal.Quotient.mk _ p) = F n p := rfl
  have hψX (n : ℕ) (j) : ψ n (Ideal.Quotient.mk _ (X j)) = Ideal.Quotient.mk _ (x j) := by
    rw [hψmk]; simp [F]
  have hψlin (n : ℕ) (i : R) (hi : i ∈ I) :
      Ideal.Quotient.mk (I ^ n) (∑ j, algebraMap A R (v.repr (I.toCotangent ⟨i, hi⟩) j) * x j) =
        ψ n (Ideal.Quotient.mk _
          (∑ j, C (v.repr (I.toCotangent ⟨i, hi⟩) j) * X j)) := by
    rw [hψmk]
    simp [F, map_sum, Ideal.Quotient.mk_algebraMap, Algebra.smul_def]
  -- `ψₙ` is surjective
  have hψsurj (n : ℕ) : Function.Surjective (ψ n) := by
    intro z
    have hz : z ∈ (ψ n).range.toSubring := by
      refine mem_of_isNilpotent (S := (ψ n).range.toSubring)
        (J := I.map (Ideal.Quotient.mk (I ^ n))) (n := n) ?_
        (fun j ↦ Ideal.Quotient.mk (I ^ n) (x j : R)) (fun j ↦ ⟨_, hψX n j⟩)
        (fun j ↦ Ideal.mem_map_of_mem _ (x j).2) ?_ ?_ z
      · rw [← Ideal.map_pow, Ideal.map_quotient_self]
      · intro w hw
        obtain ⟨i, hi, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
          Ideal.Quotient.mk_surjective).1 hw
        have : Ideal.Quotient.mk (I ^ n) i =
            ∑ j, algebraMap A _ (v.repr (I.toCotangent ⟨i, hi⟩) j) *
              Ideal.Quotient.mk (I ^ n) (x j) +
            Ideal.Quotient.mk (I ^ n)
              (i - ∑ j, algebraMap A R (v.repr (I.toCotangent ⟨i, hi⟩) j) * x j) := by
          simp only [map_sub, map_sum, map_mul, Ideal.Quotient.mk_algebraMap]
          ring
        rw [this]
        refine Submodule.add_mem_sup (Ideal.sum_mem _ fun j _ ↦
          Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)) ?_
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ (hdec i hi)
      · intro w
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective w
        refine ⟨algebraMap A _ (algebraMap R A r),
          ⟨algebraMap A _ (algebraMap R A r), AlgHom.commutes _ _⟩, ?_⟩
        rw [← Ideal.Quotient.mk_algebraMap, ← map_sub]
        exact Ideal.mem_map_of_mem _ (sub_algebraMap_mem_ker r)
    obtain ⟨q, hq⟩ := hz
    exact ⟨q, hq⟩
  -- `ψ₂` is injective
  have hψ2inj : Function.Injective (ψ 2) := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    set c0 := coeff 0 p
    set c : Fin d → A := fun j ↦ coeff (Finsupp.single j 1) p
    have hp := sub_linearPart_mem_pow_two p
    have hval : ψ 2 (Ideal.Quotient.mk _ p) =
        Ideal.Quotient.mk (I ^ 2) (algebraMap A R c0 + ∑ j, algebraMap A R (c j) * x j) := by
      rw [show (Ideal.Quotient.mk (idealOfVars (Fin d) A ^ 2) p) =
        Ideal.Quotient.mk _ (C c0 + ∑ j, C (c j) * X j) from Ideal.Quotient.eq.2 hp, hψmk]
      simp [F, map_sum, Ideal.Quotient.mk_algebraMap, Algebra.smul_def, c0, c]
    rw [hval, Ideal.Quotient.eq_zero_iff_mem] at hq
    have hc0 : c0 = 0 := by
      have := Ideal.pow_le_self two_ne_zero hq
      rw [RingHom.mem_ker, map_add, map_sum, algebraMap_algebraMap_section] at this
      simpa [map_mul, hxI] using this
    rw [hc0, map_zero, zero_add] at hq
    have hc : ∀ j, c j = 0 := by
      have h1 : I.toCotangent (∑ j, algebraMap A R (c j) • x j) = 0 := by
        rw [I.toCotangent_eq_zero]
        simpa [Submodule.coe_sum, smul_eq_mul] using hq
      simp only [map_sum, map_smul, hx, algebraMap_smul] at h1
      exact Fintype.linearIndependent_iff.1 v.linearIndependent c h1
    rw [Ideal.Quotient.eq_zero_iff_mem]
    simpa [hc0, show c = 0 from funext hc] using hp
  -- the inverse `φ₂ : R → A[X]/(X)²`
  let e2 : TruncPoly A d 2 ≃ₐ[A] R ⧸ I ^ 2 := AlgEquiv.ofBijective (ψ 2) ⟨hψ2inj, hψsurj 2⟩
  let φ2 : R →ₐ[A] TruncPoly A d 2 := e2.symm.toAlgHom.comp (Ideal.Quotient.mkₐ A (I ^ 2))
  have hφ2x (j : Fin d) : φ2 (x j) = Ideal.Quotient.mk _ (X j) := by
    apply e2.injective
    simp only [φ2, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
      AlgEquiv.apply_symm_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact (hψX 2 j).symm
  have hφ2I (i : R) (hi : i ∈ I) : φ2 i = Ideal.Quotient.mk _
      (∑ j, C (v.repr (I.toCotangent ⟨i, hi⟩) j) * X j) := by
    apply e2.injective
    simp only [φ2, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
      AlgEquiv.apply_symm_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [← hψlin 2 i hi]
    exact Ideal.Quotient.eq.2 (hdec i hi)
  refine ⟨d, fun n hn ↦ ?_⟩
  -- the lift `φₙ : R → A[X]/(X)ⁿ`
  let red : TruncPoly A d n →ₐ[A] TruncPoly A d 2 :=
    Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hn)
  have hker : RingHom.ker red = (idealOfVars (Fin d) A ^ 2).map (Ideal.Quotient.mk _) := by
    rw [← Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right (I := idealOfVars (Fin d) A) hn)]
    rfl
  set J := (idealOfVars (Fin d) A).map (Ideal.Quotient.mk (idealOfVars (Fin d) A ^ n))
  have hJn : J ^ n = ⊥ := by rw [← Ideal.map_pow, Ideal.map_quotient_self]
  have hkerJ : RingHom.ker red = J ^ 2 := by rw [hker, Ideal.map_pow]
  have hnil : IsNilpotent (RingHom.ker red) := by
    refine ⟨n, ?_⟩
    rw [hkerJ, ← pow_mul, eq_bot_iff, ← hJn]
    exact Ideal.pow_le_pow_right (by omega)
  let φ : R →ₐ[A] TruncPoly A d n := FormallySmooth.liftOfSurjective φ2 red
    (Ideal.Quotient.factor_surjective _) hnil
  have hredφ (r : R) : red (φ r) = φ2 r := FormallySmooth.liftOfSurjective_apply _ _ _ _ r
  have hφI (i : R) (hi : i ∈ I) : φ i ∈ J := by
    have h1 : φ i - Ideal.Quotient.mk _ (∑ j, C (v.repr (I.toCotangent ⟨i, hi⟩) j) * X j) ∈
        RingHom.ker red := by
      rw [RingHom.mem_ker, map_sub, hredφ, hφ2I i hi, sub_eq_zero]
      rfl
    rw [hkerJ] at h1
    have h2 : Ideal.Quotient.mk (idealOfVars (Fin d) A ^ n)
        (∑ j, C (v.repr (I.toCotangent ⟨i, hi⟩) j) * X j) ∈ J :=
      Ideal.mem_map_of_mem _ (Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _
        (Ideal.subset_span ⟨j, rfl⟩))
    have := add_mem (Ideal.pow_le_self two_ne_zero h1) h2
    rwa [sub_add_cancel] at this
  have hφIn : ∀ r ∈ I ^ n, φ r = 0 := by
    intro r hr
    have h1 : I.map φ ≤ J := Ideal.map_le_iff_le_comap.2 fun i hi ↦ hφI i hi
    have h2 := Ideal.mem_map_of_mem φ hr
    rw [Ideal.map_pow] at h2
    have h3 := Ideal.pow_right_mono h1 n h2
    rwa [hJn, Ideal.mem_bot] at h3
  let φbar : R ⧸ I ^ n →ₐ[A] TruncPoly A d n := Ideal.Quotient.liftₐ _ φ hφIn
  let g : TruncPoly A d n →ₐ[A] TruncPoly A d n := φbar.comp (ψ n)
  have hgX (j : Fin d) : g (Ideal.Quotient.mk _ (X j)) = φ (x j) := by
    simp only [g, AlgHom.comp_apply, hψX]
    rfl
  -- `g` is surjective, hence injective
  have hgsurj : Function.Surjective g := by
    intro z
    have hz : z ∈ g.range.toSubring := by
      refine mem_of_isNilpotent (S := g.range.toSubring) (J := J) hJn
        (fun j ↦ g (Ideal.Quotient.mk _ (X j))) (fun j ↦ ⟨_, rfl⟩)
        (fun j ↦ by rw [hgX]; exact hφI _ (x j).2) ?_ ?_ z
      · rw [Ideal.map_span, Ideal.span_le]
        rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
        have hj : Ideal.Quotient.mk (idealOfVars (Fin d) A ^ n) (X j) -
            g (Ideal.Quotient.mk _ (X j)) ∈ J ^ 2 := by
          rw [← hkerJ, RingHom.mem_ker, map_sub, hgX, hredφ, hφ2x, sub_eq_zero]
          rfl
        have := Submodule.add_mem_sup (Ideal.subset_span ⟨j, rfl⟩ :
          g (Ideal.Quotient.mk _ (X j)) ∈ Ideal.span (Set.range fun j ↦
            g (Ideal.Quotient.mk (idealOfVars (Fin d) A ^ n) (X j)))) hj
        rwa [add_sub_cancel] at this
      · intro w
        obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective w
        refine ⟨algebraMap A _ (coeff 0 p), ⟨algebraMap A _ (coeff 0 p), AlgHom.commutes _ _⟩, ?_⟩
        rw [← Ideal.Quotient.mk_algebraMap, ← map_sub, algebraMap_eq]
        exact Ideal.mem_map_of_mem _ (sub_C_coeff_zero_mem p)
    obtain ⟨q, hq⟩ := hz
    exact ⟨q, hq⟩
  have := (free_finite_truncPoly A d n).2
  have hginj : Function.Injective g :=
    OrzechProperty.injective_of_surjective_endomorphism g.toLinearMap hgsurj
  have hψinj : Function.Injective (ψ n) := fun p q h ↦ hginj (by simp [g, h])
  exact ⟨(AlgEquiv.ofBijective (ψ n) ⟨hψinj, hψsurj n⟩).symm⟩

variable (A R) in
/-- The infinitesimal neighbourhoods `R / Iⁿ` of a section of a formally smooth Noetherian
algebra over a local ring are flat. -/
theorem flat_quotient_pow_ker (n : ℕ) :
    Module.Flat A (R ⧸ RingHom.ker (algebraMap R A) ^ n) := by
  obtain ⟨d, hd⟩ := exists_algEquiv_truncPoly A R
  rcases lt_or_ge n 2 with h | h
  · interval_cases n
    · have : Subsingleton (R ⧸ RingHom.ker (algebraMap R A) ^ 0) :=
        Ideal.Quotient.subsingleton_iff.2 (by simp)
      infer_instance
    · let e : (R ⧸ RingHom.ker (algebraMap R A) ^ 1) ≃ₐ[A] A :=
        (Ideal.quotientEquivAlgOfEq A (pow_one _)).trans
          (Ideal.quotientKerAlgEquivOfSurjective (f := IsScalarTower.toAlgHom A R A)
            fun a ↦ ⟨algebraMap A R a, algebraMap_algebraMap_section a⟩)
      exact Module.Flat.of_linearEquiv e.toLinearEquiv
  · obtain ⟨e⟩ := hd n h
    have := (free_finite_truncPoly A d n).1
    exact Module.Flat.of_linearEquiv e.toLinearEquiv

end Main

end Algebra.FormallySmooth
