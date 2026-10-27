/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q111 and K9
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.FiniteStability
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite presentation of a finite flat graded module over a local polynomial ring

Source: Stacks Project, Tag 053C, `lemma-flat-graded-finite-type-finite-presentation-module`,
statement and proof in `literature/stacks-project/more-algebra.tex`, lines 5856--5909
(blueprint: lem-trf-local-graded-flat-module-finite-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace WeilConjectures

open scoped TensorProduct

private theorem weight_int (n : ℕ) (ω : Fin n → ℕ) (a : Fin n →₀ ℕ) :
    Finsupp.weight (fun i ↦ (ω i : ℤ)) a = (Finsupp.weight ω a : ℤ) := by
  simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum]

-- Positive weights leave only finitely many monomials in any integer degree.
private theorem homogeneous_fg {R : Type u} [CommRing R]
    (n : ℕ) (ω : Fin n → ℕ) (hω : ∀ i, 0 < ω i) (d : ℤ) :
    (MvPolynomial.weightedHomogeneousSubmodule R (fun i ↦ (ω i : ℤ)) d).FG := by
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported,
    ← Module.Finite.iff_fg]
  have hs : Set.Finite {a : Fin n →₀ ℕ |
      Finsupp.weight (fun i ↦ (ω i : ℤ)) a = d} := by
    refine (Finsupp.finite_of_nat_weight_eq ω (fun i ↦ (hω i).ne') d.toNat).subset ?_
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [weight_int] at ha
    exact congrArg Int.toNat ha
  have := hs.to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport R _)

private noncomputable def gradeProj {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (D : ℤ → Submodule R M) [DirectSum.Decomposition D] (d : ℤ) : M →ₗ[R] D d :=
  (DirectSum.component R ℤ (fun i ↦ D i) d).comp (DirectSum.decomposeLinearEquiv D).toLinearMap

private theorem gradeProj_coe {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (D : ℤ → Submodule R M) [DirectSum.Decomposition D] (d : ℤ) (x : D d) :
    gradeProj D d x = x := by
  apply Subtype.ext
  change (DirectSum.decompose D (x : M) d : M) = x
  exact DirectSum.decompose_of_mem_same D x.property

private theorem flat_piece {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]
    (D : ℤ → Submodule R M) [DirectSum.Decomposition D] (d : ℤ) :
    Module.Flat R (D d) := by
  exact Module.Flat.of_retract (D d).subtype (gradeProj D d)
    (LinearMap.ext (gradeProj_coe D d))

-- Decomposing generators does not change their polynomial span.
private theorem homogeneous_generators {R A : Type*} [CommRing R] [CommRing A]
    {M : Type*} [AddCommGroup M] [Module R M] [Module A M] [Module.Finite A M]
    (D : ℤ → Submodule R M) [DirectSum.Decomposition D] :
    ∃ s : Finset M, Submodule.span A (s : Set M) = ⊤ ∧
      ∀ x ∈ s, ∃ d, x ∈ D d := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  let t := s.biUnion fun x ↦ (DirectSum.decompose D x).support.image
    (fun d ↦ (DirectSum.decompose D x d : M))
  refine ⟨t, ?_, ?_⟩
  · apply top_unique
    rw [← hs]
    apply Submodule.span_le.mpr
    intro x hx
    rw [← DirectSum.sum_support_decompose D x]
    apply Submodule.sum_mem
    intro d hd
    apply Submodule.subset_span
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩
  · intro x hx
    obtain ⟨y, _, hy⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨d, (DirectSum.decompose D y d).property⟩

private theorem gradeProj_ne {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (D : ℤ → Submodule R M) [DirectSum.Decomposition D]
    {d e : ℤ} {x : M} (hx : x ∈ D e) (hne : e ≠ d) : gradeProj D d x = 0 := by
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_ne D hx hne

-- Project generators times polynomial coefficients onto a single degree.
private theorem piece_fg {R : Type*} [CommRing R]
    (n : ℕ) (ω : Fin n → ℕ) (hω : ∀ i, 0 < ω i)
    {M : Type*} [AddCommGroup M] [Module R M]
    [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (D : ℤ → Submodule R M) [DirectSum.Decomposition D]
    (hg : ∀ e d p x,
      p ∈ MvPolynomial.weightedHomogeneousSubmodule R (fun i ↦ (ω i : ℤ)) e →
      x ∈ D d → p • x ∈ D (e + d))
    {ι : Type*} [Finite ι] (m : ι → M) (δ : ι → ℤ) (hm : ∀ i, m i ∈ D (δ i))
    (hspan : Submodule.span (MvPolynomial (Fin n) R) (Set.range m) = ⊤) (d : ℤ) :
    (D d).FG := by
  classical
  let C := MvPolynomial.weightedHomogeneousSubmodule R (fun i ↦ (ω i : ℤ))
  let Q : Submodule R M := ⨆ i, (C (d - δ i)).map
    ((LinearMap.toSpanSingleton (MvPolynomial (Fin n) R) M (m i)).restrictScalars R)
  have hQ : Q.FG := Submodule.fg_iSup _ fun i ↦ (homogeneous_fg n ω hω _).map _
  have hproj : ∀ x ∈ Submodule.span (MvPolynomial (Fin n) R) (Set.range m),
      ∀ p : MvPolynomial (Fin n) R, (gradeProj D d (p • x) : M) ∈ Q := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro p
      let := MvPolynomial.weightedDecomposition R (fun i ↦ (ω i : ℤ))
      induction p using DirectSum.Decomposition.inductionOn
        (MvPolynomial.weightedHomogeneousSubmodule R (fun i ↦ (ω i : ℤ))) with
      | zero => simp
      | homogeneous p =>
        rename_i e
        have hp := hg e (δ i) p (m i) p.property (hm i)
        by_cases he : e + δ i = d
        · have hmem : (p : MvPolynomial (Fin n) R) ∈ C (d - δ i) := by
            have : e = d - δ i := by omega
            simpa only [C, this] using p.property
          have hpd : (p : MvPolynomial (Fin n) R) • m i ∈ D d := he ▸ hp
          rw [show gradeProj D d ((p : MvPolynomial (Fin n) R) • m i) =
            ⟨(p : MvPolynomial (Fin n) R) • m i, hpd⟩ from gradeProj_coe D d ⟨_, hpd⟩]
          exact (le_iSup (fun i ↦ (C (d - δ i)).map
            ((LinearMap.toSpanSingleton (MvPolynomial (Fin n) R) M (m i)).restrictScalars R)) i)
            ⟨p, hmem, rfl⟩
        · rw [gradeProj_ne D hp he]
          exact Q.zero_mem
      | add p q hp hq => simpa only [add_smul, map_add, Submodule.coe_add] using Q.add_mem hp hq
    | zero => intro p; simp
    | add x y _ _ hx hy =>
      intro p
      simpa only [smul_add, map_add, Submodule.coe_add] using Q.add_mem (hx p) (hy p)
    | smul a x _ hx => intro p; simpa only [← mul_smul] using hx (p * a)
  have hDQ : D d ≤ Q := by
    intro x hx
    simpa only [one_smul, gradeProj_coe D d ⟨x, hx⟩] using
      hproj x (hspan ▸ Submodule.mem_top) 1
  have hQD : Q ≤ D d := by
    apply iSup_le
    intro i x hx
    obtain ⟨p, hp, rfl⟩ := hx
    change p • m i ∈ D d
    simpa only [sub_add_cancel] using hg (d - δ i) (δ i) p (m i) hp (hm i)
  exact (le_antisymm hDQ hQD) ▸ hQ

private theorem homogeneous_span {R : Type*} [CommRing R]
    (n : ℕ) (ω : Fin n → ℕ)
    {M : Type*} [AddCommGroup M] [Module R M]
    [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (D : ℤ → Submodule R M) [DirectSum.Decomposition D]
    (hg : ∀ e d p x,
      p ∈ MvPolynomial.weightedHomogeneousSubmodule R (fun i ↦ (ω i : ℤ)) e →
      x ∈ D d → p • x ∈ D (e + d))
    (s : Finset M) (hs : ∀ x ∈ s, ∃ d, x ∈ D d) (d : ℤ)
    {x : M} (hx : x ∈ Submodule.span (MvPolynomial (Fin n) R) (s : Set M)) :
    (gradeProj D d x : M) ∈ Submodule.span (MvPolynomial (Fin n) R) (s : Set M) := by
  classical
  let N := Submodule.span (MvPolynomial (Fin n) R) (s : Set M)
  have H : ∀ x ∈ N, ∀ p : MvPolynomial (Fin n) R, (gradeProj D d (p • x) : M) ∈ N := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he⟩ := hs x hx
      intro p
      let := MvPolynomial.weightedDecomposition R (fun i ↦ (ω i : ℤ))
      induction p using DirectSum.Decomposition.inductionOn
        (MvPolynomial.weightedHomogeneousSubmodule R (fun i ↦ (ω i : ℤ))) with
      | zero => simp
      | homogeneous p =>
        rename_i a
        have hp := hg a e p x p.property he
        by_cases h : a + e = d
        · have hpd : (p : MvPolynomial (Fin n) R) • x ∈ D d := h ▸ hp
          rw [gradeProj_coe D d ⟨_, hpd⟩]
          exact N.smul_mem _ (Submodule.subset_span hx)
        · rw [gradeProj_ne D hp h]; exact N.zero_mem
      | add p q hp hq => simpa only [add_smul, map_add, Submodule.coe_add] using N.add_mem hp hq
    | zero => intro p; simp
    | add x y _ _ hx hy =>
      intro p
      simpa only [smul_add, map_add, Submodule.coe_add] using N.add_mem (hx p) (hy p)
    | smul a x _ hx => intro p; simpa only [← mul_smul] using hx (p * a)
  simpa only [one_smul] using H x hx 1

-- Graded Nakayama: finite pieces let us lift generation from the closed fibre.
private theorem fg_of_finite_fiber {R : Type*} [CommRing R] [IsLocalRing R]
    (n : ℕ) (ω : Fin n → ℕ)
    {M : Type*} [AddCommGroup M] [Module R M]
    [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (D : ℤ → Submodule R M) [DirectSum.Decomposition D]
    (hg : ∀ e d p x,
      p ∈ MvPolynomial.weightedHomogeneousSubmodule R (fun i ↦ (ω i : ℤ)) e →
      x ∈ D d → p • x ∈ D (e + d))
    (hfin : ∀ d, Module.Finite R (D d))
    [Module.Finite (MvPolynomial (Fin n) R) (M ⊗[R] IsLocalRing.ResidueField R)] :
    Module.Finite (MvPolynomial (Fin n) R) M := by
  classical
  let k := IsLocalRing.ResidueField R
  let P := MvPolynomial (Fin n) R
  let q : M →ₗ[P] M ⊗[R] k :=
    { toFun := fun x ↦ x ⊗ₜ[R] (1 : k)
      map_add' := fun x y ↦ TensorProduct.add_tmul x y 1
      map_smul' := fun a x ↦ rfl }
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨x, hx⟩ := TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective
      (TensorProduct.comm R M k z)
    exact ⟨x, (TensorProduct.comm R M k).injective (by simpa [q] using hx)⟩
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := P) (M := M ⊗[R] k)
  choose lift hlift using hq
  let s₀ := t.image lift
  let s := s₀.biUnion fun x ↦ (DirectSum.decompose D x).support.image
    (fun d ↦ (DirectSum.decompose D x d : M))
  have hs : ∀ x ∈ s, ∃ d, x ∈ D d := by
    intro x hx
    obtain ⟨y, _, hy⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨d, (DirectSum.decompose D y d).property⟩
  let N := Submodule.span P (s : Set M)
  have hN : N.map q = ⊤ := by
    apply top_unique
    rw [← ht]
    apply Submodule.span_le.mpr
    intro y hy
    refine ⟨lift y, ?_, hlift y⟩
    rw [← DirectSum.sum_support_decompose D (lift y)]
    apply N.sum_mem
    intro d hd
    exact Submodule.subset_span (Finset.mem_biUnion.mpr ⟨lift y,
      Finset.mem_image.mpr ⟨y, hy, rfl⟩, Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩)
  have htop : N = ⊤ := by
    apply top_unique
    intro x _
    rw [← DirectSum.sum_support_decompose D x]
    apply N.sum_mem
    intro d _
    have := hfin d
    let Nd : Submodule R (D d) := (N.restrictScalars R).comap (D d).subtype
    have hNd : Nd = ⊤ := by
      apply (IsLocalRing.map_tensorProduct_mk_eq_top (R := R)).mp
      apply top_unique
      intro z _
      obtain ⟨a, rfl⟩ := TensorProduct.mk_surjective R (D d) k Ideal.Quotient.mk_surjective z
      have ha : q (a : M) ∈ N.map q := hN ▸ Submodule.mem_top
      obtain ⟨b, hb, hab⟩ := ha
      refine ⟨gradeProj D d b, ?_, ?_⟩
      · exact homogeneous_span n ω D hg s hs d hb
      · have H := congrArg (fun z ↦ TensorProduct.comm R (D d) k
          ((gradeProj D d).rTensor k z)) hab
        simpa only [q, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.rTensor_tmul,
          gradeProj_coe, TensorProduct.comm_tmul, TensorProduct.mk_apply] using H
    have : DirectSum.decompose D x d ∈ Nd := hNd ▸ Submodule.mem_top
    exact this
  exact ⟨s, htop⟩

private theorem noetherian_restrict_surjective
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [IsNoetherian B M] (h : Function.Surjective (algebraMap A B)) : IsNoetherian A M := by
  constructor
  intro N
  let N' : Submodule B M :=
    { toAddSubmonoid := N.toAddSubmonoid
      smul_mem' := by
        intro b x hx
        obtain ⟨a, rfl⟩ := h b
        change (algebraMap A B a) • x ∈ N
        simpa only [algebraMap_smul] using N.smul_mem a hx }
  exact (IsNoetherian.noetherian N').restrictScalars_of_surjective h

-- Work over the polynomial ring tensored with the residue field, then restrict scalars.
private theorem noetherian_free_fiber {R : Type*} [CommRing R] [IsLocalRing R]
    (n : ℕ) {ι : Type*} [Finite ι] :
    IsNoetherian (MvPolynomial (Fin n) R)
      ((ι → MvPolynomial (Fin n) R) ⊗[R] IsLocalRing.ResidueField R) := by
  classical
  let := Fintype.ofFinite ι
  let P := MvPolynomial (Fin n) R
  let k := IsLocalRing.ResidueField R
  let B := P ⊗[R] k
  have : IsNoetherianRing (k ⊗[R] P) := Algebra.FiniteType.isNoetherianRing k _
  have : IsNoetherianRing B := isNoetherianRing_of_ringEquiv _
    (Algebra.TensorProduct.comm R k P).toRingEquiv
  have hsurj : Function.Surjective (algebraMap P B) :=
    Algebra.TensorProduct.includeLeft_surjective P P Ideal.Quotient.mk_surjective
  have : IsNoetherian P B := noetherian_restrict_surjective hsurj
  let f : ((ι → P) ⊗[R] k) →ₗ[P] (ι → B) :=
    LinearMap.pi fun i ↦ TensorProduct.AlgebraTensorModule.map
      (LinearMap.proj i : (ι → P) →ₗ[P] P) (LinearMap.id : k →ₗ[R] k)
  have hf : Function.Injective f := by
    have heq (z : (ι → P) ⊗[R] k) :
        f z = TensorProduct.piLeft R k (fun _ : ι ↦ P) z := by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x a => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    intro x y hxy
    apply (TensorProduct.piLeft R k (fun _ : ι ↦ P)).injective
    rw [← heq, ← heq, hxy]
  exact isNoetherian_of_injective f hf

-- Orthogonal projections and spanning pieces certify an internal direct sum.
private theorem internal_of_projections {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (D : ℤ → Submodule R M)
    (π : ∀ d, M →ₗ[R] D d)
    (hsame : ∀ d (x : D d), π d x = x)
    (hne : ∀ d e (x : D e), e ≠ d → π d x = 0)
    (htop : iSup D = ⊤) : DirectSum.IsInternal D := by
  have hcomp (d : ℤ) : (π d).comp (DirectSum.coeLinearMap D) =
      DirectSum.component R ℤ (fun i ↦ D i) d := by
    apply DirectSum.linearMap_ext
    intro e
    apply LinearMap.ext
    intro x
    by_cases h : e = d
    · subst e
      simpa using hsame d x
    · simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof]
      change π d (x : M) = ((DFinsupp.lapply (R := R) (M := fun i ↦ D i) d).comp
        (DFinsupp.lsingle e)) x
      rw [DFinsupp.lapply_comp_lsingle_of_ne _ _ (Ne.symm h)]
      exact hne d e x h
  constructor
  · intro x y hxy
    apply DFinsupp.ext
    intro d
    change DirectSum.coeLinearMap D x = DirectSum.coeLinearMap D y at hxy
    have H := congrArg (π d) hxy
    change (π d).comp (DirectSum.coeLinearMap D) x =
      (π d).comp (DirectSum.coeLinearMap D) y at H
    rw [hcomp] at H
    exact H
  · change Function.Surjective (DirectSum.coeLinearMap D)
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, htop]

-- A submodule stable under degree projections inherits the decomposition.
private theorem submodule_internal {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (D : ℤ → Submodule R M) [DirectSum.Decomposition D]
    (K : Submodule A M) (hK : ∀ d (x : K), (gradeProj D d (x : M) : M) ∈ K) :
    DirectSum.IsInternal (fun d ↦ (D d).comap (K.subtype.restrictScalars R)) := by
  classical
  let E := fun d ↦ (D d).comap (K.subtype.restrictScalars R)
  let π : ∀ d, K →ₗ[R] E d := fun d ↦
    { toFun := fun x ↦ ⟨⟨gradeProj D d (x : M), hK d x⟩, (gradeProj D d (x : M)).property⟩
      map_add' := fun x y ↦ by apply Subtype.ext; apply Subtype.ext; simp
      map_smul' := fun a x ↦ by apply Subtype.ext; apply Subtype.ext; simp }
  apply internal_of_projections E π
  · intro d x
    apply Subtype.ext; apply Subtype.ext
    change (gradeProj D d ((x : K) : M) : M) = ((x : K) : M)
    exact congrArg (fun z : D d ↦ (z : M))
      (gradeProj_coe D d ⟨_, x.property⟩)
  · intro d e x h
    apply Subtype.ext; apply Subtype.ext
    change (gradeProj D d ((x : K) : M) : M) = 0
    exact congrArg (fun z : D d ↦ (z : M)) (gradeProj_ne D x.property h)
  · apply top_unique
    intro x _
    have hx : x = ∑ d ∈ (DirectSum.decompose D (x : M)).support,
        (⟨gradeProj D d (x : M), hK d x⟩ : K) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum]
      change (x : M) = ∑ d ∈ (DirectSum.decompose D (x : M)).support,
        (DirectSum.decompose D (x : M) d : M)
      exact (DirectSum.sum_support_decompose D (x : M)).symm
    rw [hx]
    apply Submodule.sum_mem
    intro d _
    exact (le_iSup E d) (gradeProj D d (x : M)).property

private theorem graded_map_proj {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (D : ℤ → Submodule R M) [DirectSum.Decomposition D]
    (E : ℤ → Submodule R N) [DirectSum.Decomposition E] (f : M →ₗ[R] N)
    (hf : ∀ d (x : D d), f x ∈ E d) (d : ℤ) (x : M) :
    f (gradeProj D d x) = (gradeProj E d (f x) : N) := by
  classical
  induction x using DirectSum.Decomposition.inductionOn D with
  | zero => simp
  | homogeneous x =>
    rename_i e
    by_cases h : e = d
    · subst e
      rw [gradeProj_coe D d x, gradeProj_coe E d ⟨_, hf d x⟩]
    · rw [gradeProj_ne D x.property h, gradeProj_ne E (hf e x) h]
      simp
  | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]

-- The grading on a finite free module whose generators have degrees δ.
private def shiftedPieces {R : Type*} [CommRing R] (n : ℕ) (ω : Fin n → ℕ)
    {ι : Type*} (δ : ι → ℤ) (d : ℤ) : Submodule R (ι → MvPolynomial (Fin n) R) where
  carrier := {x | ∀ i, x i ∈
    MvPolynomial.weightedHomogeneousSubmodule R (fun i ↦ (ω i : ℤ)) (d - δ i)}
  zero_mem' := fun _i ↦ Submodule.zero_mem _
  add_mem' := fun hx hy i ↦ Submodule.add_mem _ (hx i) (hy i)
  smul_mem' := fun a _x hx i ↦ Submodule.smul_mem _ a (hx i)

private theorem shiftedPieces_internal {R : Type*} [CommRing R]
    (n : ℕ) (ω : Fin n → ℕ) {ι : Type*} [Finite ι] (δ : ι → ℤ) :
    DirectSum.IsInternal (shiftedPieces (R := R) n ω δ) := by
  classical
  let := Fintype.ofFinite ι
  let C := MvPolynomial.weightedHomogeneousSubmodule R (fun i ↦ (ω i : ℤ))
  let π : ∀ d, (ι → MvPolynomial (Fin n) R) →ₗ[R] shiftedPieces n ω δ d := fun d ↦
    { toFun := fun x ↦ ⟨fun i ↦ MvPolynomial.weightedHomogeneousComponent
        (fun i ↦ (ω i : ℤ)) (d - δ i) (x i),
        fun i ↦ MvPolynomial.weightedHomogeneousComponent_mem _ _ _⟩
      map_add' := fun x y ↦ by ext i; simp
      map_smul' := fun a x ↦ by ext i; simp }
  apply internal_of_projections _ π
  · intro d x
    apply Subtype.ext
    funext i
    exact MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same (x.property i)
  · intro d e x h
    apply Subtype.ext
    funext i
    exact MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne _
      (x.property i) (by omega)
  · apply top_unique
    intro x _
    rw [← LinearMap.sum_single_apply (fun _ : ι ↦ MvPolynomial (Fin n) R) x]
    apply Submodule.sum_mem
    intro i _
    let := MvPolynomial.weightedDecomposition R (fun i ↦ (ω i : ℤ))
    have H : ∀ p : MvPolynomial (Fin n) R,
        Pi.single i p ∈ ⨆ d, shiftedPieces n ω δ d := by
      intro p
      induction p using DirectSum.Decomposition.inductionOn C with
      | zero => simp
      | homogeneous p =>
        rename_i e
        apply (le_iSup (shiftedPieces n ω δ) (e + δ i))
        intro j
        by_cases h : j = i
        · subst j; simpa only [Pi.single_eq_same, add_sub_cancel_right] using p.property
        · simp [Pi.single_eq_of_ne h]
      | add p q hp hq => simpa only [Pi.single_add] using Submodule.add_mem _ hp hq
    exact H (x i)

private theorem shiftedPieces_finite {R : Type*} [CommRing R]
    (n : ℕ) (ω : Fin n → ℕ) (hω : ∀ i, 0 < ω i)
    {ι : Type*} [Finite ι] (δ : ι → ℤ) (d : ℤ) :
    Module.Finite R (shiftedPieces (R := R) n ω δ d) := by
  let C := MvPolynomial.weightedHomogeneousSubmodule R (fun i ↦ (ω i : ℤ))
  have : ∀ i, Module.Finite R (C (d - δ i)) := fun i ↦
    Module.Finite.of_fg (homogeneous_fg n ω hω _)
  let e : shiftedPieces (R := R) n ω δ d ≃ₗ[R] (∀ i, C (d - δ i)) :=
    { toFun := fun x i ↦ ⟨x.val i, x.property i⟩
      invFun := fun x ↦ ⟨fun i ↦ (x i : MvPolynomial (Fin n) R), fun i ↦ (x i).property⟩
      left_inv := fun x ↦ rfl
      right_inv := fun x ↦ rfl
      map_add' := fun x y ↦ rfl
      map_smul' := fun a x ↦ rfl }
  exact Module.Finite.equiv e.symm

/-- A finite graded module over a positively weighted polynomial ring over a local ring is
finitely presented if it is flat over the coefficient ring.

Source: Stacks Project, Tag 053C, `lemma-flat-graded-finite-type-finite-presentation-module`,
statement at lines 5856--5870 and proof at lines 5871--5909
(blueprint: lem-trf-local-graded-flat-module-finite-presentation).

The integer-weighted homogeneous submodules of Mathlib are exactly the spans of the monomials
of the indicated weighted degree. Positive weights make all negative-degree pieces zero.
`Ldeg` is an internal direct-sum decomposition by coefficient-ring submodules, with the stated
compatibility with homogeneous scalar multiplication.

Proof:
1. Replace finite generators by their homogeneous components, and form the shifted finite free
   surjection `f : F → L`. Weighted projections construct the internal grading on `F` and on
   its kernel `K`. Positivity makes each polynomial homogeneous piece finite over `R`.
2. Project polynomial linear combinations of the homogeneous generators to show `L_d` is finite.
   It is a retract of the flat module `L`, hence flat and therefore free over the local ring.
   Thus it is finitely presented. The kernel of the surjection `F_d → L_d` is finite because
   `F_d` is finite and `L_d` is finitely presented. This kernel identifies with `K_d`.
3. Tensor the presentation with the residue field `κ`. Flatness of `L` makes `K ⊗ κ → F ⊗ κ`
   injective. The finite-type `κ`-algebra `P ⊗ κ` is Noetherian, so `F ⊗ κ`, and hence its
   submodule `K ⊗ κ`, is Noetherian over `P`. Lift finitely many residue generators to `K`
   and replace the lifts by their homogeneous components.
4. Their polynomial span `N` is stable under projections and maps onto `K ⊗ κ`. Applying the
   degree projection shows `N ∩ K_d` maps onto `κ ⊗ K_d`. Nakayama gives `N ∩ K_d = K_d`
   because `K_d` is finite. Summing components gives `N = K`, and the finite free surjection
   with finitely generated kernel yields a finite presentation.
-/
theorem local_graded_flat_module_finite_presentation
    {R : Type u} [CommRing R] [IsLocalRing R]
    (n : ℕ) (ω : Fin n → ℕ) (hω : ∀ i : Fin n, 0 < ω i)
    {L : Type v} [AddCommGroup L] [Module (MvPolynomial (Fin n) R) L] [Module R L]
    [IsScalarTower R (MvPolynomial (Fin n) R) L]
    (Ldeg : ℤ → Submodule R L) (hLinternal : DirectSum.IsInternal Ldeg)
    (hgraded : ∀ (e d : ℤ) (p : MvPolynomial (Fin n) R) (x : L),
      p ∈ MvPolynomial.weightedHomogeneousSubmodule R (fun i : Fin n ↦ (ω i : ℤ)) e →
      x ∈ Ldeg d → p • x ∈ Ldeg (e + d))
    [Module.Finite (MvPolynomial (Fin n) R) L] [Module.Flat R L] :
    Module.FinitePresentation (MvPolynomial (Fin n) R) L := by
  classical
  let P := MvPolynomial (Fin n) R
  let := hLinternal.chooseDecomposition
  obtain ⟨s, hs, hshom⟩ := homogeneous_generators (A := P) Ldeg
  choose δ hδ using fun i : s ↦ hshom i i.property
  let m : s → L := fun i ↦ i
  have hm : Submodule.span P (Set.range m) = ⊤ := by simpa [m] using hs
  let F := s → P
  let D := shiftedPieces (R := R) n ω δ
  let := (shiftedPieces_internal (R := R) n ω δ).chooseDecomposition
  let f : F →ₗ[P] L := Fintype.linearCombination P m
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hm
  have hfd : ∀ d (x : D d), f x ∈ Ldeg d := by
    intro d x
    change (∑ i : s, (x : F) i • m i) ∈ Ldeg d
    apply Submodule.sum_mem
    intro i _
    have H := hgraded (d - δ i) (δ i) ((x : F) i) (m i) (x.property i) (hδ i)
    simpa only [sub_add_cancel] using H
  have hDgraded : ∀ e d p (x : F),
      p ∈ MvPolynomial.weightedHomogeneousSubmodule R (fun i ↦ (ω i : ℤ)) e →
      x ∈ D d → p • x ∈ D (e + d) := by
    intro e d p x hp hx i
    change p * x i ∈ MvPolynomial.weightedHomogeneousSubmodule R
      (fun i ↦ (ω i : ℤ)) ((e + d) - δ i)
    have H := MvPolynomial.weightedHomogeneousSubmodule_mul
      (w := fun i : Fin n ↦ (ω i : ℤ)) e (d - δ i)
      (Submodule.mul_mem_mul hp (hx i))
    simpa only [Pi.smul_apply, smul_eq_mul, add_sub_assoc] using H
  let K := LinearMap.ker f
  have hK : ∀ d (x : K), (gradeProj D d (x : F) : F) ∈ K := by
    intro d x
    change f (gradeProj D d (x : F)) = 0
    have H := graded_map_proj D Ldeg (f.restrictScalars R) hfd d (x : F)
    change f (gradeProj D d (x : F)) = (gradeProj Ldeg d (f x) : L) at H
    rw [H]
    change (gradeProj Ldeg d (f x) : L) = 0
    rw [x.property, map_zero, Submodule.coe_zero]
  let E := fun d ↦ (D d).comap (K.subtype.restrictScalars R)
  let := (submodule_internal D K hK).chooseDecomposition
  have hEgraded : ∀ e d p (x : K),
      p ∈ MvPolynomial.weightedHomogeneousSubmodule R (fun i ↦ (ω i : ℤ)) e →
      x ∈ E d → p • x ∈ E (e + d) := by
    intro e d p x hp hx
    exact hDgraded e d p x hp hx
  have hEfinite : ∀ d, Module.Finite R (E d) := by
    intro d
    have : Module.Finite R (D d) := shiftedPieces_finite n ω hω δ d
    have : Module.Finite R (Ldeg d) := Module.Finite.of_fg
      (piece_fg n ω hω Ldeg hgraded m δ hδ hm d)
    have : Module.Flat R (Ldeg d) := flat_piece Ldeg d
    have : Module.Free R (Ldeg d) := Module.free_of_flat_of_isLocalRing
    have : Module.FinitePresentation R (Ldeg d) :=
      Module.finitePresentation_of_projective R (Ldeg d)
    let g : D d →ₗ[R] Ldeg d :=
      (f.restrictScalars R ∘ₗ (D d).subtype).codRestrict (Ldeg d) (hfd d)
    have hg : Function.Surjective g := by
      intro x
      obtain ⟨y, hy⟩ := hf x
      refine ⟨gradeProj D d y, ?_⟩
      apply Subtype.ext
      change f (gradeProj D d y) = x
      have H := graded_map_proj D Ldeg (f.restrictScalars R) hfd d y
      change f (gradeProj D d y) = (gradeProj Ldeg d (f y) : L) at H
      rw [H, hy, gradeProj_coe]
    have : Module.Finite R (LinearMap.ker g) :=
      Module.Finite.of_fg (Module.FinitePresentation.fg_ker g hg)
    let e : E d ≃ₗ[R] LinearMap.ker g :=
      { toFun := fun x ↦ ⟨⟨((x : K) : F), x.property⟩,
          Subtype.ext ((x : K).property)⟩
        invFun := fun x ↦ ⟨⟨((x : D d) : F), congrArg Subtype.val x.property⟩,
          (x : D d).property⟩
        left_inv := fun x ↦ rfl
        right_inv := fun x ↦ rfl
        map_add' := fun x y ↦ rfl
        map_smul' := fun a x ↦ rfl }
    exact Module.Finite.equiv e.symm
  let k := IsLocalRing.ResidueField R
  have : IsNoetherian P (F ⊗[R] k) := noetherian_free_fiber n
  let j : (K ⊗[R] k) →ₗ[P] (F ⊗[R] k) :=
    TensorProduct.AlgebraTensorModule.map K.subtype (LinearMap.id : k →ₗ[R] k)
  have hj : Function.Injective j := by
    have H := LinearMap.lTensor_injective_of_exact_of_flat (f.restrictScalars R) hf
      (K.subtype.restrictScalars R) Subtype.val_injective
      (by
        rw [LinearMap.exact_iff]
        ext x
        constructor
        · intro hx
          exact ⟨⟨x, hx⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          exact x.property) k
    intro x y hxy
    apply (TensorProduct.comm R K k).injective
    apply H
    have hx (z : K ⊗[R] k) :
        (K.subtype.restrictScalars R).lTensor k (TensorProduct.comm R K k z) =
          TensorProduct.comm R F k (j z) := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x a => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [hx, hx, hxy]
  have : IsNoetherian P (K ⊗[R] k) := isNoetherian_of_injective j hj
  have : Module.Finite P (K ⊗[R] k) := inferInstance
  have : Module.Finite P K := fg_of_finite_fiber n ω E hEgraded hEfinite
  exact Module.finitePresentation_of_free_of_surjective f hf (Module.Finite.iff_fg.mp
    (inferInstance : Module.Finite P K))

end WeilConjectures

