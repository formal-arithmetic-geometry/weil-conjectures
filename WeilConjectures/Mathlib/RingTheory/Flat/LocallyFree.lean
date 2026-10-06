/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Support

/-!
# Modules of constant fibre dimension over a reduced ring

Let `R` be a reduced ring and `M` a finite `R`-module whose fibres `κ(p) ⊗[R] M` all have the
same dimension `n`. Then `M` is locally free of rank `n`. Near a prime `p`, elements of `M`
lifting a basis of `κ(p) ⊗[R] M` define a map `φ : Rⁿ → M` with cokernel killed by some
`a ∉ p` (Nakayama); every element of the kernel of `φ` lies, after multiplying by `a`, in every
prime of `R`, since `φ` is injective on all fibres where it is surjective, by the dimension
count. As `R` is reduced, `φ` is an isomorphism after inverting `a`.

## Main results

- `Module.exists_free_away_of_finrank_fiber_eq`: `M` is free after inverting some `a ∉ p`.
- `Module.projective_of_finrank_fiber_eq`: if `M` is finitely presented, it is projective.
- `Module.rankAtStalk_eq_of_finrank_fiber_eq`: its rank is `n` everywhere.

## Blueprint

These are the commutative-algebra content of `lem-sc-finite-constant-length-flat`.
-/

@[expose] public section

open TensorProduct

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If `a` annihilates the cokernel of `φ : N → M` and `a` is nonzero in the field `k`, then
`φ` becomes surjective after base change to `k`. -/
lemma surjective_baseChange_of_smul_mem_range {N : Type*} [AddCommGroup N] [Module R N]
    {k : Type*} [Field k] [Algebra R k] (φ : N →ₗ[R] M) {a : R}
    (ha : ∀ m : M, a • m ∈ LinearMap.range φ) (hak : algebraMap R k a ≠ 0) :
    Function.Surjective (φ.baseChange k) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul s m =>
    obtain ⟨c, hc⟩ := ha m
    refine ⟨(s * (algebraMap R k a)⁻¹) ⊗ₜ c, ?_⟩
    rw [LinearMap.baseChange_tmul, hc, tmul_smul, smul_tmul', Algebra.smul_def, mul_comm,
      mul_assoc, inv_mul_cancel₀ hak, mul_one]


variable [IsReduced R] [Module.Finite R M] {n : ℕ}

/-- Let `R` be reduced and `M` a finite `R`-module all of whose fibres `κ(q) ⊗[R] M` have
dimension `n`. Then every prime `p` has a basic open neighbourhood `D(a)` on which `M` is free:
elements of `M` lifting a basis of `κ(p) ⊗[R] M` give an isomorphism `R_aⁿ ≅ M_a`. -/
theorem exists_free_away_of_finrank_fiber_eq
    (h : ∀ (q : Ideal R) [q.IsPrime], finrank q.ResidueField (q.Fiber M) = n)
    (p : Ideal R) [p.IsPrime] :
    ∃ a ∉ p, Module.Free (Localization.Away a) (LocalizedModule.Away a M) := by
  classical
  have : Nontrivial R :=
    nontrivial_of_ne 0 1 fun h ↦ ‹p.IsPrime›.ne_top ((p.eq_top_iff_one).mpr (h ▸ p.zero_mem))
  let k := p.ResidueField
  -- A basis of `κ(p) ⊗ M` consisting of elements `1 ⊗ m`.
  let S : Set (k ⊗[R] M) := Set.range fun m : M ↦ (1 : k) ⊗ₜ[R] m
  have hS : Submodule.span k S = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul s m =>
      rw [show s ⊗ₜ[R] m = s • ((1 : k) ⊗ₜ[R] m) by rw [smul_tmul', smul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent k S
  let b : Basis t k (k ⊗[R] M) := Basis.mk hli (by rw [Subtype.range_coe, hspan, hS])
  have : Finite t := Module.Finite.finite_basis b
  let _ : Fintype t := Fintype.ofFinite t
  have hcard : Fintype.card t = n := by rw [← Module.finrank_eq_card_basis b]; exact h p
  choose v hv using fun i : t ↦ htS i.2
  let φ : (t → R) →ₗ[R] M := Fintype.linearCombination R v
  -- The cokernel of `φ` vanishes after tensoring with `κ(p)`, hence near `p`.
  have hv' (i : t) : v i ∈ LinearMap.range φ :=
    ⟨Pi.single i 1, by simp [φ]⟩
  have hzero : ((LinearMap.range φ).mkQ.baseChange k) = 0 := by
    refine b.ext fun i ↦ ?_
    rw [Basis.mk_apply, ← hv i, LinearMap.baseChange_tmul, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).mpr (hv' i), tmul_zero, LinearMap.zero_apply]
  have hsub : Subsingleton (k ⊗[R] (M ⧸ LinearMap.range φ)) := by
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective k (LinearMap.range φ).mkQ_surjective x
    obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective k (LinearMap.range φ).mkQ_surjective y
    have e (z : k ⊗[R] M) : ((LinearMap.range φ).mkQ.lTensor k) z = 0 :=
      congr($hzero z)
    rw [e, e]
  have hp : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∉
      Module.support R (M ⧸ LinearMap.range φ) := by
    rwa [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton]
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus, Set.not_subset] at hp
  obtain ⟨a, haC, hap⟩ := hp
  have ha (m : M) : a • m ∈ LinearMap.range φ := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact Module.mem_annihilator.mp haC _
  -- `a` kills the kernel of `φ`.
  have hker (c : t → R) (hc : φ c = 0) (i : t) : a * c i = 0 := by
    have : a * c i ∈ nilradical R := by
      rw [nilradical_eq_sInf, Submodule.mem_sInf]
      intro (q : Ideal R) (hq : q.IsPrime)
      by_cases haq : a ∈ q
      · exact Ideal.mul_mem_right _ q haq
      refine Ideal.mul_mem_left q _ ?_
      have hak : algebraMap R q.ResidueField a ≠ 0 := by
        rwa [ne_eq, Ideal.algebraMap_residueField_eq_zero]
      have hinj : Function.Injective (φ.baseChange q.ResidueField) := by
        refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr
          (surjective_baseChange_of_smul_mem_range φ ha hak)
        rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card, hcard]
        exact (h q).symm
      have h1 : (1 : q.ResidueField) ⊗ₜ[R] c = 0 :=
        hinj (by rw [LinearMap.baseChange_tmul, hc, tmul_zero, map_zero])
      have h2 := congr(AlgebraTensorModule.rid R q.ResidueField q.ResidueField
        ((LinearMap.proj i).baseChange q.ResidueField $h1))
      simp only [LinearMap.baseChange_tmul, LinearMap.proj_apply, map_zero,
        AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one] at h2
      exact Ideal.algebraMap_residueField_eq_zero.mp h2
    rwa [nilradical_eq_zero, Submodule.zero_eq_bot, Ideal.mem_bot] at this
  refine ⟨a, hap, ?_⟩
  have : Module.Free (Localization.Away a) (LocalizedModule.Away a (t → R)) :=
    free_of_isLocalizedModule (Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) (t → R))
  let ψ := LocalizedModule.map (Submonoid.powers a) φ
  let a' : Submonoid.powers a := ⟨a, Submonoid.mem_powers a⟩
  refine Module.Free.of_equiv (LinearEquiv.ofBijective ψ ⟨?_, ?_⟩)
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using LocalizedModule.induction_on with
    | h c s =>
      rw [LocalizedModule.map_mk, ← LocalizedModule.zero_mk s, LocalizedModule.mk_eq] at hx
      obtain ⟨u, hu⟩ := hx
      rw [smul_zero, smul_zero, smul_smul, Submonoid.smul_def, ← map_smul] at hu
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
      refine ⟨a' * (u * s), ?_⟩
      ext i
      simpa [a', Submonoid.smul_def, mul_assoc] using hker _ hu i
  · intro x
    induction x using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨c, hc⟩ := ha m
      refine ⟨LocalizedModule.mk c (a' * s), ?_⟩
      rw [LocalizedModule.map_mk, hc, ← LocalizedModule.mk_cancel_common_left a' s m]
      rfl

/-- Blueprint `lem-sc-finite-constant-length-flat` (algebraic form): a finitely presented module
of constant fibre dimension over a reduced ring is projective, hence flat. -/
theorem projective_of_finrank_fiber_eq [Module.FinitePresentation R M]
    (h : ∀ (q : Ideal R) [q.IsPrime], finrank q.ResidueField (q.Fiber M) = n) :
    Module.Projective R M := by
  rw [← freeLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro p
  obtain ⟨a, hap, _⟩ := exists_free_away_of_finrank_fiber_eq h p.asIdeal
  exact basicOpen_subset_freeLocus_iff.mpr inferInstance hap

/-- Blueprint `lem-sc-finite-constant-length-flat` (algebraic form): a finitely presented module
of constant fibre dimension `n` over a reduced ring has rank `n` at every prime. -/
theorem rankAtStalk_eq_of_finrank_fiber_eq [Module.FinitePresentation R M]
    (h : ∀ (q : Ideal R) [q.IsPrime], finrank q.ResidueField (q.Fiber M) = n)
    (p : PrimeSpectrum R) : rankAtStalk M p = n := by
  have := projective_of_finrank_fiber_eq h
  rw [rankAtStalk_eq]
  exact h _

end Module
