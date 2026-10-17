/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.RingTheory.MvPolynomial.Basic
public import WeilConjectures.ScratchCDBSH
public import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension.SubalgebraLimit
public import WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension

/-!
# The local calculation in the affine Artin vanishing theorem

Let `K` be a field, `P` a regular finitely generated `K`-domain of dimension `d`, `s` a geometric
point of `Spec P` lying on the divisor `u = 0` of a nonzero `u ∈ P`, whose residue field has
transcendence degree at least `a` over `K`, and `R` the strict henselization of `P` at `s`.
Assuming the affine Artin bound in dimensions `< d`
(`AlgebraicGeometry.Scheme.ArtinBound`), we show `cd_tor(Spec R[1/u]) ≤ d - a`
(`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_strictHenselization_away`).

This is the local calculation of the blueprint proof of `thm-sc-affine-torsion-cd`. Lifts
`τ₁, …, τₐ ∈ P` of algebraically independent elements of the residue field embed `K(τ)` into
the henselian local domain `R`, whose integral closure `F` of `K(τ)` is a separably closed field
(`exists_isSepClosed_of_henselianLocalRing`). The local equation `u` gives an embedding
`F(x) ⟶ R[1/u]`, `x ↦ u`, and `R[1/u]` is the filtered union of its finitely generated
`F(x)`-subalgebras, of dimension at most `d - a - 1` by a transcendence degree count. Since
`cd_tor(F(x)) ≤ 1`, the induction hypothesis bounds their torsion cohomological dimension by
`d - a`, and the bound passes to the limit.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

/-- Evaluating a polynomial in several variables at `Fin.cons x₀ x` is evaluating, at `x₀`, its
image under `MvPolynomial.finSuccEquiv` with coefficients evaluated at `x`. -/
theorem MvPolynomial.aeval_cons_eq_eval₂_finSuccEquiv {K A : Type*} [CommRing K] [CommRing A]
    [Algebra K A] {a : ℕ} (x₀ : A) (x : Fin a → A) (p : MvPolynomial (Fin (a + 1)) K) :
    aeval (Fin.cons x₀ x) p = (finSuccEquiv K a p).eval₂ (aeval x).toRingHom x₀ := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [finSuccEquiv_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, hp, map_mul, Polynomial.eval₂_mul]
    congr 1
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [finSuccEquiv_X_zero]
    · simp [finSuccEquiv_X_succ]

/-- In a local ring `R`, a polynomial over a ring `A`, evaluated through `g : A ⟶ R`, at an
element `u` of the maximal ideal is a unit as soon as the image of its constant term is. -/
theorem Polynomial.isUnit_eval₂_of_isUnit_coeff_zero {A R : Type*} [CommRing A] [CommRing R]
    [IsLocalRing R] (g : A →+* R) {u : R} (hu : u ∈ IsLocalRing.maximalIdeal R) (q : A[X])
    (h : IsUnit (g (q.coeff 0))) : IsUnit (q.eval₂ g u) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hom_eval₂,
    (IsLocalRing.residue_eq_zero_iff u).2 hu, eval₂_at_zero, RingHom.comp_apply]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 h

/-- Let `R` be a local `K`-algebra, `u` an element of its maximal ideal and `S = R[1/u]`
nontrivial. If `τ₁, …, τₐ ∈ R` are such that every nonzero polynomial in them is a unit, then
`u, τ₁, …, τₐ` are algebraically independent over `K` in `S`: a nonzero polynomial in them is a
power of `u` times a unit. -/
theorem algebraicIndependent_cons_of_mem_maximalIdeal {K R S : Type*} [Field K] [CommRing R]
    [IsLocalRing R] [Algebra K R] [CommRing S] [Nontrivial S] [Algebra R S] [Algebra K S]
    [IsScalarTower K R S] {u : R} (hu : u ∈ IsLocalRing.maximalIdeal R)
    [IsLocalization.Away u S] {a : ℕ} (τ : Fin a → R)
    (hτ : ∀ f : MvPolynomial (Fin a) K, f ≠ 0 → IsUnit (MvPolynomial.aeval τ f)) :
    AlgebraicIndependent K
      (Fin.cons (algebraMap R S u) (fun i ↦ algebraMap R S (τ i)) : Fin (a + 1) → S) := by
  rw [algebraicIndependent_iff]
  intro p hp
  by_contra hp0
  have hx : (Fin.cons (algebraMap R S u) (fun i ↦ algebraMap R S (τ i)) : Fin (a + 1) → S) =
      algebraMap R S ∘ (Fin.cons u τ : Fin (a + 1) → R) := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  rw [hx, MvPolynomial.aeval_algebraMap_apply, MvPolynomial.aeval_cons_eq_eval₂_finSuccEquiv]
    at hp
  set q := MvPolynomial.finSuccEquiv K a p
  have hq : q ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (AlgEquiv.injective _)]
  obtain ⟨q', hq'⟩ : X ^ q.natTrailingDegree ∣ q :=
    X_pow_dvd_iff.2 fun d hd ↦ coeff_eq_zero_of_lt_natTrailingDegree hd
  have hq0 : q'.coeff 0 ≠ 0 := by
    have := congrArg (fun r ↦ r.coeff q.natTrailingDegree) hq'
    simp only [coeff_X_pow_mul', le_refl, ↓reduceIte, Nat.sub_self] at this
    rw [← this]
    exact mt trailingCoeff_eq_zero.1 hq
  rw [hq', eval₂_mul, eval₂_X_pow, map_mul, map_pow] at hp
  have hunit : IsUnit (algebraMap R S u ^ q.natTrailingDegree *
      algebraMap R S (q'.eval₂ (MvPolynomial.aeval τ).toRingHom u)) :=
    ((IsLocalization.Away.algebraMap_isUnit u).pow _).mul
      ((Polynomial.isUnit_eval₂_of_isUnit_coeff_zero _ hu q' (hτ _ hq0)).map _)
  exact hunit.ne_zero hp

namespace AlgebraicGeometry.Scheme

/-- The affine Artin bound in dimension `e`: for every field `L` with `cd_tor(L) ≤ c` and every
affine `L`-scheme `X` of finite type and dimension at most `e`, `cd_tor(X) ≤ e + c`. -/
def ArtinBound (e : ℕ) : Prop :=
  ∀ (L : Type u) [Field L] (c : ℕ), (Spec (.of L)).HasTorsionCohomologicalDimensionLE c →
    ∀ (X : Scheme.{u}) (a : X ⟶ Spec (.of L)), LocallyOfFiniteType a → IsAffine X →
      topologicalKrullDim X ≤ (e : WithBot ℕ∞) → X.HasTorsionCohomologicalDimensionLE (e + c)
/-- **The local calculation.** Let `K` be a field, `P` a regular finitely generated `K`-domain
of dimension `d`, and assume the affine Artin bound in all dimensions `< d`. Let `s` be a
geometric point of `Spec P`, `x ∈ P` nonzero vanishing at `s`, and `τ₁, …, τₐ ∈ P` whose values
at `s` are algebraically independent over `K`. Then the localization `R[1/x]` of the strict
henselization `R` of `P` at `s` satisfies `cd_tor(Spec R[1/x]) ≤ d - a`. -/
theorem hasTorsionCohomologicalDimensionLE_strictHenselization_away {K : Type u} [Field K]
    {P : CommRingCat.{u}} [Algebra K P] [Algebra.FiniteType K P] [IsDomain P] [IsRegularRing P]
    {d : ℕ} (hd : ringKrullDim P = d) (IH : ∀ e < d, ArtinBound.{u} e)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Spec P) {x : P} (hx0 : x ≠ 0)
    (hx : (Spec.preimage s).hom x = 0) {a : ℕ} (τ : Fin a → P)
    (hτ : ∀ f : MvPolynomial (Fin a) K, f ≠ 0 →
      (Spec.preimage s).hom (MvPolynomial.aeval τ f) ≠ 0) :
    (Spec (.of (Localization.Away ((toStrictHenselization s).hom x)))).HasTorsionCohomologicalDimensionLE
      (d - a) := by
  classical
  set R := strictHenselization s
  set φ := (toStrictHenselization s).hom
  have : IsDomain R := isDomain_strictHenselization s
  have hφ : Function.Injective φ := injective_toStrictHenselization s
  have heval (y : P) : (strictHenselizationEval s).hom (φ y) = (Spec.preimage s).hom y := by
    rw [← CommRingCat.comp_apply, toStrictHenselization_comp_strictHenselizationEval]
  let S := Localization.Away (φ x)
  have hφx : φ x ≠ 0 := by rwa [ne_eq, map_eq_zero_iff _ hφ]
  have hpow : Submonoid.powers (φ x) ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hφx
  have : IsDomain S := IsLocalization.isDomain_localization hpow
  let : Algebra P R := φ.toAlgebra
  let : Algebra K R := (φ.comp (algebraMap K P)).toAlgebra
  have : IsScalarTower K P R := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K P S := IsScalarTower.of_algebraMap_eq fun k ↦ by
    rw [IsScalarTower.algebraMap_apply P R S, IsScalarTower.algebraMap_apply K R S,
      IsScalarTower.algebraMap_apply K P R]
  -- polynomials in the `τᵢ` are units of `R`
  have haeval (f : MvPolynomial (Fin a) K) :
      MvPolynomial.aeval (fun i ↦ φ (τ i)) f = φ (MvPolynomial.aeval τ f) :=
    (MvPolynomial.aeval_algebraMap_apply (R := K) (S₁ := P) R τ f).symm
  have hτR (f : MvPolynomial (Fin a) K) (hf : f ≠ 0) :
      IsUnit (MvPolynomial.aeval (fun i ↦ φ (τ i)) f) := by
    rw [isUnit_iff_strictHenselizationEval_ne_zero, haeval, heval]
    exact hτ f hf
  have hxm : φ x ∈ IsLocalRing.maximalIdeal R :=
    (mem_maximalIdeal_strictHenselization_iff _).2 (by rw [heval, hx])
  have hind := algebraicIndependent_cons_of_mem_maximalIdeal (K := K) (S := S) hxm
    (fun i ↦ φ (τ i)) hτR
  -- `trdeg_K S = d`
  have hPS : Function.Injective (algebraMap P S) := (IsLocalization.injective S hpow).comp hφ
  have : Algebra.IsAlgebraic P R := isAlgebraic_strictHenselization s
  have : Algebra.IsAlgebraic R S := IsLocalization.isAlgebraic (Submonoid.powers (φ x))
  have : Algebra.IsAlgebraic P S := Algebra.IsAlgebraic.trans P R S
  have : FaithfulSMul P S := (faithfulSMul_iff_algebraMap_injective P S).2 hPS
  have hKS : Algebra.trdeg K S = d := by
    rw [← Algebra.trdeg_add_eq K P S, Algebra.trdeg_eq_zero (R := P) (A := S), add_zero,
      Algebra.trdeg_eq_of_ringKrullDim_eq K P hd]
  have had : a + 1 ≤ d := by
    have := hind.cardinalMk_le_trdeg
    rw [hKS, Cardinal.mk_fin] at this
    exact_mod_cast this
  -- the separably closed field `F ⊆ R`
  let k₀ := FractionRing (MvPolynomial (Fin a) K)
  let ψ : MvPolynomial (Fin a) K →+* R := (MvPolynomial.aeval (fun i ↦ φ (τ i))).toRingHom
  have hψ (p : nonZeroDivisors (MvPolynomial (Fin a) K)) : IsUnit (ψ p) :=
    hτR _ (nonZeroDivisors.coe_ne_zero p)
  let θ : k₀ →+* R := IsLocalization.lift hψ
  let : Algebra k₀ R := θ.toAlgebra
  obtain ⟨F, _, _, _, _, _⟩ := exists_isSepClosed_of_henselianLocalRing k₀ R
  obtain ⟨ρ, hρX, hρC⟩ := exists_ratFunc_ringHom_of_mem_maximalIdeal (F := F) hxm S
  sorry

end AlgebraicGeometry.Scheme
