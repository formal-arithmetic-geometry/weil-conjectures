/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NC and R8, Claude
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Noetherian generic freeness for an algebra-module pair

Source: Stacks Project, Algebra, Tag 051R, `lemma-generic-flatness-Noetherian`
(blueprint: lem-pur-noetherian-algebra-module-generic-freeness).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Module

private theorem free_away_of_dvd {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {a b : R} (h : a ∣ b)
    [Module.Free (Localization.Away a) (LocalizedModule.Away a M)] :
    Module.Free (Localization.Away b) (LocalizedModule.Away b M) := by
  obtain ⟨c, rfl⟩ := h
  let A := Localization.Away a
  let B := Localization.Away (a * c)
  let : Algebra A B := (IsLocalization.Away.awayToAwayRight a c).toAlgebra
  have : IsScalarTower R A B := .of_algebraMap_eq fun r ↦
    (IsLocalization.Away.awayToAwayRight_eq a c r).symm
  let e := (LinearEquiv.baseChange A B _ _ (LocalizedModule.equivTensorProduct (.powers a) M)).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M)
  have : Module.Free B (TensorProduct A B (LocalizedModule.Away a M)) := inferInstance
  exact Module.Free.of_equiv
    (e.trans (LocalizedModule.equivTensorProduct (.powers (a * c)) M).symm)

private theorem free_localized_of_equiv {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (a : R) (e : M ≃ₗ[R] N)
    [Module.Free (Localization.Away a) (LocalizedModule.Away a M)] :
    Module.Free (Localization.Away a) (LocalizedModule.Away a N) := by
  let e' := (LocalizedModule.equivTensorProduct (.powers a) M).trans
    ((LinearEquiv.baseChange R (Localization.Away a) _ _ e).trans
      (LocalizedModule.equivTensorProduct (.powers a) N).symm)
  exact Module.Free.of_equiv e'

set_option backward.isDefEq.respectTransparency false in
private theorem free_of_exhaustive_filtration {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (N : ℕ → Submodule R M) (hN : Monotone N)
    (htop : ∀ m : M, ∃ i, m ∈ N i) [Module.Free R (N 0)]
    (hQ : ∀ i, Module.Free R (↥(N (i + 1)) ⧸ (N i).comap (N (i + 1)).subtype)) :
    Module.Free R M := by
  classical
  have hstep (i : ℕ) : ∃ C : Submodule R M, Module.Free R C ∧
      C ≤ N (i + 1) ∧ Disjoint C (N i) ∧ N i ⊔ C = N (i + 1) := by
    let K := (N i).comap (N (i + 1)).subtype
    have : Module.Free R (↥(N (i + 1)) ⧸ K) := hQ i
    obtain ⟨s, hs⟩ := K.mkQ.exists_rightInverse_of_surjective K.range_mkQ
    have hs' (q) : K.mkQ (s q) = q := DFunLike.congr_fun hs q
    let t := (N (i + 1)).subtype ∘ₗ s
    have ht : Function.Injective t :=
      (N (i + 1)).injective_subtype.comp (Function.LeftInverse.injective hs')
    refine ⟨LinearMap.range t, Module.Free.of_equiv (LinearEquiv.ofInjective t ht),
      ?_, ?_, ?_⟩
    · rintro _ ⟨q, rfl⟩
      exact (s q).2
    · rw [Submodule.disjoint_def]
      rintro _ ⟨q, rfl⟩ hq
      have hzero : K.mkQ (s q) = 0 := by
        rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      rw [hs'] at hzero
      simp [hzero, t]
    · apply le_antisymm
      · exact sup_le (hN (Nat.le_succ i)) (by rintro _ ⟨q, rfl⟩; exact (s q).2)
      · intro m hm
        let y : N (i + 1) := ⟨m, hm⟩
        have hy : y - s (K.mkQ y) ∈ K := by
          have hz : K.mkQ (y - s (K.mkQ y)) = 0 := by
            rw [map_sub, hs', sub_self]
          exact (Submodule.Quotient.mk_eq_zero K).mp hz
        exact Submodule.mem_sup.mpr
          ⟨y - s (K.mkQ y), hy, t (K.mkQ y), ⟨_, rfl⟩, by simp [t, y]⟩
  choose C hfree hle hdisj hsup using hstep
  let D : ℕ → Submodule R M
    | 0 => N 0
    | n + 1 => C n
  let : ∀ n : ℕ, AddCommMonoid ↥(D n) := fun n ↦ (D n).addCommMonoid
  let : ∀ n : ℕ, Module R ↥(D n) := fun n ↦ (D n).module
  have hDfree (n : ℕ) : Module.Free R ↥(D n) := by
    cases n with
    | zero => exact inferInstanceAs (Module.Free R (N 0))
    | succ n => exact hfree n
  have hDle (n : ℕ) : D n ≤ N n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact hle n
  have hind : iSupIndep D := by
    rw [iSupIndep_iff_supIndep]
    intro S
    induction S using Finset.induction_on_max with
    | empty => exact Finset.supIndep_empty _
    | insert n S hmax ih =>
      apply ih.insert
      cases n with
      | zero =>
        have : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun j hj ↦ by
          have := hmax j hj
          omega
        simp [this]
      | succ n =>
        apply (hdisj n).mono_right
        exact Finset.sup_le fun j hj ↦ (hDle j).trans (hN (by
          have := hmax j hj
          omega))
  have hspan : ⨆ n, D n = ⊤ := by
    apply eq_top_iff.mpr
    intro m _
    obtain ⟨i, hi⟩ := htop m
    have hNi : ∀ i, N i ≤ ⨆ n, D n := by
      intro i
      induction i with
      | zero => exact le_iSup D 0
      | succ i ih =>
        rw [← hsup i]
        exact sup_le ih (le_iSup D (i + 1))
    exact hNi i hi
  have : ∀ i, Module.Free R ↥(D i) := hDfree
  exact Module.Free.of_equiv (hind.linearEquiv hspan)

private theorem free_localized_of_filtration {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (a : R) (N : ℕ → Submodule R M)
    (hN : Monotone N) (htop : ∀ m : M, ∃ i, m ∈ N i)
    [Module.Free (Localization.Away a) (LocalizedModule.Away a (N 0))]
    (hQ : ∀ i, Module.Free (Localization.Away a)
      (LocalizedModule.Away a (↥(N (i + 1)) ⧸ (N i).comap (N (i + 1)).subtype))) :
    Module.Free (Localization.Away a) (LocalizedModule.Away a M) := by
  let S := Submonoid.powers a
  let A := Localization S
  let L := LocalizedModule S M
  let P : ℕ → Submodule A L := fun i ↦ (N i).localized S
  have hP : Monotone P := by
    intro i j hij
    exact (Submodule.localized'gi A S (LocalizedModule.mkLinearMap S M)).gc.monotone_l (hN hij)
  have hPtop : ∀ m : L, ∃ i, m ∈ P i := by
    intro m
    induction m using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨i, hi⟩ := htop m
      refine ⟨i, (Submodule.mem_localized' A S _ _ _).mpr ⟨m, hi, s, ?_⟩⟩
      exact (IsLocalizedModule.mk_eq_mk' s m).symm
  have : Module.Free A ↥(P 0) :=
    Module.Free.of_equiv ((N 0).localizedEquiv S).symm
  apply free_of_exhaustive_filtration P hP hPtop
  intro i
  let K := (N i).comap (N (i + 1)).subtype
  let Q := ↥(N (i + 1)) ⧸ K
  let f₀ := (N i).toLocalized S
  let f₁ := (N (i + 1)).toLocalized S
  let f₂ := LocalizedModule.mkLinearMap S Q
  let j := Submodule.inclusion (hN (Nat.le_succ i))
  let j' := Submodule.inclusion (hP (Nat.le_succ i))
  let q := IsLocalizedModule.map S f₁ f₂ K.mkQ
  have hj : IsLocalizedModule.map S f₀ f₁ j = j'.restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext S f₀ f₁
    apply LinearMap.ext
    intro m
    change IsLocalizedModule.map S f₀ f₁ j (f₀ m) = j' (f₀ m)
    rw [IsLocalizedModule.map_apply]
    rfl
  have hex : Function.Exact j K.mkQ := by
    intro m
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨fun hm ↦ ⟨⟨m, hm⟩, rfl⟩, fun ⟨x, hx⟩ ↦ hx ▸ x.2⟩
  have hex' : Function.Exact j' q := by
    have := IsLocalizedModule.map_exact S f₀ f₁ f₂ j K.mkQ hex
    rwa [hj] at this
  let q' : ↥(P (i + 1)) →ₗ[A] LocalizedModule S Q :=
    q.extendScalarsOfIsLocalization S A
  have hker : LinearMap.ker q' = (P i).comap (P (i + 1)).subtype := by
    ext m
    change q m = 0 ↔ m.val ∈ P i
    rw [hex' m]
    exact ⟨fun ⟨x, hx⟩ ↦ hx ▸ x.2, fun hm ↦ ⟨⟨m, hm⟩, rfl⟩⟩
  have hsurj : Function.Surjective q' :=
    IsLocalizedModule.map_surjective S f₁ f₂ K.mkQ K.mkQ_surjective
  have : Module.Free A (LocalizedModule S Q) := hQ i
  exact Module.Free.of_equiv
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (q'.quotKerEquivOfSurjective hsurj)).symm

/-- Generic freeness for finite modules over a polynomial ring in `n` variables, by induction on
`n` (Stacks, Tag 051R). -/
private lemma exists_freeAway_of_mvPolynomial (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsDomain R] (n : ℕ) :
    ∀ (A : Type*) [CommRing A] [Algebra R A], Nonempty (MvPolynomial (Fin n) R ≃ₐ[R] A) →
      ∀ (M : Type*) [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
        [Module.Finite A M],
        ∃ a : R, a ≠ 0 ∧ Module.Free (Localization.Away a) (LocalizedModule.Away a M) := by
  induction n with
  | zero =>
    intro A _ _ ⟨e⟩ M _ _ _ _ _
    have e' : R ≃ₐ[R] A := (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm.trans e
    have : Module.Finite R A := Module.Finite.equiv e'.toLinearEquiv
    have : Module.Finite R M := Module.Finite.trans A M
    let K := FractionRing R
    let f := LocalizedModule.mkLinearMap (nonZeroDivisors R) M
    have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
    have : Module.Free K (LocalizedModule (nonZeroDivisors R) M) := inferInstance
    obtain ⟨a, ha, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
      (nonZeroDivisors R) f K
    exact ⟨a, nonZeroDivisors.ne_zero ha, hfree⟩
  | succ n ih =>
    intro A _ _ ⟨e⟩ M _ _ _ _ _
    have : IsNoetherianRing A := isNoetherianRing_of_ringEquiv _ e.toRingEquiv
    -- The subalgebra `T` generated by the first `n` variables, and the last variable `x`.
    let ι : MvPolynomial (Fin n) R →ₐ[R] A :=
      e.toAlgHom.comp (MvPolynomial.rename Fin.castSucc)
    have hι : Function.Injective ι :=
      e.injective.comp (MvPolynomial.rename_injective _ (Fin.castSucc_injective n))
    let T : Subalgebra R A := ι.range
    have eT : MvPolynomial (Fin n) R ≃ₐ[R] T := AlgEquiv.ofInjective ι hι
    have : IsNoetherianRing T := isNoetherianRing_of_ringEquiv _ eT.toRingEquiv
    let x : A := e (MvPolynomial.X (Fin.last n))
    have hT (i : Fin n) : e (MvPolynomial.X i.castSucc) ∈ T :=
      ⟨MvPolynomial.X i, by simp [ι]⟩
    have hgen : ∀ y : A, y ∈ Algebra.adjoin T {x} := by
      intro y
      obtain ⟨p, rfl⟩ := e.surjective y
      induction p using MvPolynomial.induction_on with
      | C r =>
        rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, IsScalarTower.algebraMap_apply R T A]
        exact Subalgebra.algebraMap_mem _ _
      | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
      | mul_X p i hp =>
        rw [map_mul]
        refine Subalgebra.mul_mem _ hp ?_
        induction i using Fin.lastCases with
        | last => exact Algebra.subset_adjoin rfl
        | cast i => exact Subalgebra.algebraMap_mem (Algebra.adjoin T {x}) (⟨_, hT i⟩ : T)
    -- The filtration `M i = span_T {x^j m | j ≤ i, m ∈ σ}`.
    obtain ⟨σ, hσ⟩ := Module.Finite.fg_top (R := A) (M := M)
    classical
    let gens (i : ℕ) : Finset M :=
      (Finset.range (i + 1) ×ˢ σ).image fun jm ↦ x ^ jm.1 • jm.2
    let N (i : ℕ) : Submodule T M := Submodule.span T (gens i)
    have hgens_mono : Monotone gens := by
      intro i j hij
      apply Finset.image_subset_image
      apply Finset.product_subset_product_left
      exact Finset.range_subset_range.mpr (by omega)
    have hN : Monotone N := fun i j hij ↦ Submodule.span_mono (by exact_mod_cast hgens_mono hij)
    have hxN (i : ℕ) : ∀ y ∈ N i, x • y ∈ N (i + 1) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨⟨j, m⟩, hjm, rfl⟩ := Finset.mem_image.mp hy
        simp only [Finset.mem_product, Finset.mem_range] at hjm
        apply Submodule.subset_span
        refine Finset.mem_image.mpr ⟨(j + 1, m), ?_, ?_⟩
        · simp only [Finset.mem_product, Finset.mem_range]
          exact ⟨by omega, hjm.2⟩
        · simp [pow_succ', mul_smul]
      | zero => simp
      | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
      | smul t y _ hy =>
        rw [smul_comm]
        exact Submodule.smul_mem _ t hy
    have htop : ∀ m : M, ∃ i, m ∈ N i := by
      have hU : ∀ y : A, ∀ m : M, (∃ i, m ∈ N i) → ∃ i, y • m ∈ N i := by
        intro y
        induction hgen y using Algebra.adjoin_induction with
        | mem y hy =>
          rw [Set.mem_singleton_iff] at hy
          subst hy
          rintro m ⟨i, hi⟩
          exact ⟨i + 1, hxN i m hi⟩
        | algebraMap t =>
          rintro m ⟨i, hi⟩
          exact ⟨i, by rw [algebraMap_smul]; exact Submodule.smul_mem _ t hi⟩
        | add y z _ _ hy hz =>
          intro m hm
          obtain ⟨i, hi⟩ := hy m hm
          obtain ⟨j, hj⟩ := hz m hm
          exact ⟨max i j, by
            rw [add_smul]
            exact Submodule.add_mem _ (hN (le_max_left i j) hi) (hN (le_max_right i j) hj)⟩
        | mul y z _ _ hy hz =>
          intro m hm
          obtain ⟨i, hi⟩ := hz m hm
          rw [mul_smul]
          exact hy _ ⟨i, hi⟩
      intro m
      have hm : m ∈ Submodule.span A (σ : Set M) := hσ ▸ trivial
      induction hm using Submodule.span_induction with
      | mem m hm =>
        exact ⟨0, Submodule.subset_span (Finset.mem_image.mpr
          ⟨(0, m), Finset.mem_product.mpr ⟨by simp, hm⟩, by simp⟩)⟩
      | zero => exact ⟨0, zero_mem _⟩
      | add y z _ _ hy hz =>
        obtain ⟨i, hi⟩ := hy
        obtain ⟨j, hj⟩ := hz
        exact ⟨max i j, Submodule.add_mem _ (hN (le_max_left i j) hi) (hN (le_max_right i j) hj)⟩
      | smul y m _ hm => exact hU y m hm
    -- Multiplication by `x ^ k` raises the filtration degree by `k`.
    let μ (k : ℕ) : M →ₗ[T] M := (LinearMap.lsmul A M (x ^ k)).restrictScalars T
    have hμ (k : ℕ) : ∀ i, ∀ y ∈ N i, μ k y ∈ N (i + k) := by
      induction k with
      | zero => intro i y hy; simpa [μ] using hy
      | succ k ih' =>
        intro i y hy
        have := hxN _ _ (ih' i y hy)
        simpa [μ, pow_succ', mul_smul, ← add_assoc] using this
    -- The graded pieces `Q i = N (i + 1) ⧸ N i` are quotients of `Q 0` via `x ^ i`.
    let Q (i : ℕ) := ↥(N (i + 1)) ⧸ (N i).comap (N (i + 1)).subtype
    let ψ (i : ℕ) : ↥(N 1) →ₗ[T] Q i :=
      ((N i).comap (N (i + 1)).subtype).mkQ ∘ₗ
        (μ i).restrict (p := N 1) (q := N (i + 1)) fun y hy ↦ by
          simpa [add_comm] using hμ i 1 y hy
    have hψ (i : ℕ) : (N 0).comap (N 1).subtype ≤ LinearMap.ker (ψ i) := by
      intro y hy
      rw [LinearMap.mem_ker]
      erw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      simpa [Submodule.mem_comap] using hμ i 0 y hy
    let Θ (i : ℕ) : Q 0 →ₗ[T] Q i := ((N 0).comap (N 1).subtype).liftQ (ψ i) (hψ i)
    have hΘ (i : ℕ) : Function.Surjective (Θ i) := by
      intro z
      induction z using Submodule.Quotient.induction_on with
      | H z =>
        have hle : N (i + 1) ≤ N i ⊔ (N 1).map (μ i) := by
          rw [Submodule.span_le]
          intro w hw
          obtain ⟨⟨j, m⟩, hjm, rfl⟩ := Finset.mem_image.mp hw
          simp only [Finset.mem_product, Finset.mem_range] at hjm
          rcases Nat.lt_or_ge j (i + 1) with hj | hj
          · apply Submodule.mem_sup_left
            apply Submodule.subset_span
            exact Finset.mem_image.mpr ⟨(j, m), by simp [hjm.2, hj], rfl⟩
          · obtain rfl : j = i + 1 := by omega
            apply Submodule.mem_sup_right
            refine ⟨x • m, Submodule.subset_span (Finset.mem_image.mpr ⟨(1, m), ?_, ?_⟩), ?_⟩
            · simp [hjm.2]
            · simp
            · simp [μ, smul_smul, ← pow_succ']
        obtain ⟨u, hu, _, ⟨y, hy, rfl⟩, hz⟩ := Submodule.mem_sup.mp (hle z.2)
        refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, ?_⟩
        erw [Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.eq, Submodule.mem_comap]
        have h' : (μ i) y - (z : M) = -u := by rw [← hz]; abel
        simpa [LinearMap.coe_restrict_apply, h'] using (N i).neg_mem hu
    let L (i : ℕ) : Submodule T (Q 0) := LinearMap.ker (Θ i)
    have hL : Monotone L := by
      refine monotone_nat_of_le_succ fun i v hv ↦ ?_
      induction v using Submodule.Quotient.induction_on with
      | H y =>
        change Θ i _ = 0 at hv
        change Θ (i + 1) _ = 0
        erw [Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero] at hv ⊢
        rw [Submodule.mem_comap] at hv ⊢
        have := hxN i _ hv
        simpa [μ, pow_succ', mul_smul] using this
    have : IsNoetherian T (Q 0) := inferInstance
    obtain ⟨i₀, hi₀⟩ := monotone_stabilizes_iff_noetherian.mpr this ⟨L, hL⟩
    have hker (i : ℕ) : LinearMap.ker (Θ i) = L (min i i₀) := by
      rcases le_total i i₀ with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h]
        exact (hi₀ i h).symm
    -- Apply the induction hypothesis to `N 0` and to the quotients `Q 0 ⧸ L j`, `j ≤ i₀`.
    obtain ⟨a₀, ha₀, h₀⟩ := ih T ⟨eT⟩ (N 0)
    have hQ (j : ℕ) : ∃ b : R, b ≠ 0 ∧
        Module.Free (Localization.Away b) (LocalizedModule.Away b (Q 0 ⧸ L j)) :=
      ih T ⟨eT⟩ _
    choose b hb₀ hb using hQ
    set a := a₀ * ∏ j ∈ Finset.range (i₀ + 1), b j
    have ha : a ≠ 0 := mul_ne_zero ha₀ (Finset.prod_ne_zero_iff.mpr fun j _ ↦ hb₀ j)
    have hQa (i : ℕ) : Module.Free (Localization.Away a) (LocalizedModule.Away a (Q i)) := by
      have hj : min i i₀ ∈ Finset.range (i₀ + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_right _ _))
      have : Module.Free (Localization.Away (b (min i i₀)))
          (LocalizedModule.Away (b (min i i₀)) (Q 0 ⧸ L (min i i₀))) := hb _
      have : Module.Free (Localization.Away a)
          (LocalizedModule.Away a (Q 0 ⧸ L (min i i₀))) :=
        free_away_of_dvd (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem b hj) _)
      let e₁ : (Q 0 ⧸ L (min i i₀)) ≃ₗ[T] Q i :=
        (Submodule.quotEquivOfEq _ _ (hker i).symm).trans
          ((Θ i).quotKerEquivOfSurjective (hΘ i))
      exact free_localized_of_equiv a (e₁.restrictScalars R)
    have : Module.Free (Localization.Away a₀) (LocalizedModule.Away a₀ (N 0)) := h₀
    have : Module.Free (Localization.Away a) (LocalizedModule.Away a (N 0)) :=
      free_away_of_dvd (a := a₀) (Dvd.intro _ rfl)
    have : Module.Free (Localization.Away a)
        (LocalizedModule.Away a ((N 0).restrictScalars R)) :=
      free_localized_of_equiv a (((N 0).restrictScalarsEquiv R).symm.restrictScalars R)
    refine ⟨a, ha, free_localized_of_filtration a (fun i ↦ (N i).restrictScalars R)
      (fun i j hij ↦ hN hij) htop ?_⟩
    intro i
    let K := (N i).comap (N (i + 1)).subtype
    have : Module.Free (Localization.Away a) (LocalizedModule.Away a (Q i)) := hQa i
    exact free_localized_of_equiv a
      (Submodule.Quotient.restrictScalarsEquiv R K).symm

/-- Stacks Project, Algebra, Tag 051R, `lemma-generic-flatness-Noetherian`.
(blueprint: lem-pur-noetherian-algebra-module-generic-freeness)
A finite module over a finite type algebra over a Noetherian domain becomes free over the
localized base after inverting a nonzero scalar. The basis need not be finite.

Proof: choose a finite polynomial presentation of the algebra and restrict scalars along its
surjection. Induct on the number of polynomial variables. With no variables, a finite module
is finitely presented; its fraction-field localization is a vector space, and Mathlib spreads
its basis to one principal localization.

For the induction step, write the polynomial algebra as T[x], with T having one fewer variable.
Choose finite module generators and let N i be the T-span of their multiples by powers of x
of degree at most i. This filtration is exhaustive. Multiplication by x^i gives a surjection
from Q 0 = N 1 / N 0 onto Q i = N (i+1) / N i. Its kernels form an increasing sequence in
the finite T-module Q 0, so they stabilize. Consequently only finitely many quotient modules
need to be made free. Apply induction to these and to N 0, and multiply their nonzero
localization elements. Localization preserves the filtration quotients. Each localized
successive quotient is free, so the quotient map splits; the resulting independent free
complements span the entire localized module and give a basis.

The polynomial filtration and stabilization argument is adapted from the proved generic
flatness argument `exists_flatAway_of_mvPolynomial` in
`WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus`. The splitting and direct-sum
argument upgrades that construction to freeness; no generic-flatness theorem is used. -/
theorem noetherian_algebra_module_generic_freeness
    (R : Type u) (B : Type v) (M : Type w)
    [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [AddCommGroup M] [Module B M] [Module R M] [IsScalarTower R B M]
    [Module.Finite B M] :
    ∃ a : R, a ≠ 0 ∧ Module.Free (Localization.Away a) (LocalizedModule.Away a M) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  let := Module.compHom M f.toRingHom
  have : IsScalarTower R (MvPolynomial (Fin n) R) M := by
    refine ⟨fun r p m ↦ ?_⟩
    change f (r • p) • m = r • f p • m
    rw [map_smul, smul_assoc]
  have : Module.Finite (MvPolynomial (Fin n) R) M := by
    obtain ⟨σ, hσ⟩ := Module.Finite.fg_top (R := B) (M := M)
    refine ⟨⟨σ, eq_top_iff.mpr fun m hm' ↦ ?_⟩⟩
    clear hm'
    have hm : m ∈ Submodule.span B (σ : Set M) := hσ ▸ trivial
    induction hm using Submodule.span_induction with
    | mem m hm => exact Submodule.subset_span hm
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul s m _ hm =>
      obtain ⟨p, rfl⟩ := hf s
      exact Submodule.smul_mem _ p hm
  obtain ⟨a, ha, h⟩ := exists_freeAway_of_mvPolynomial R n (MvPolynomial (Fin n) R)
    ⟨AlgEquiv.refl⟩ M
  exact ⟨a, ha, h⟩

end Module
