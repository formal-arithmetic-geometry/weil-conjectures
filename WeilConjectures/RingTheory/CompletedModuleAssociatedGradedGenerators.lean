/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.RingTheory.AssociatedGradedRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Degree-zero generators for the associated graded of a completed module

Source: Stacks Project, Cohomology of Schemes, Lemma 087Z,
`lemma-finite-over-rees-algebra`, affine assertion in its proof; Algebra, Lemma 05GG
(blueprint: lem-weil-pbc-completed-module-associated-graded-generators).

For an ideal `J` of `A` and an `A`-module `M` we introduce the pieces
`gr^n_J(M) = J^n M / J^(n+1) M` of the associated graded module and the graded scalar
multiplication `gr^n_J(A) × gr^m_J(M) → gr^(n+m)_J(M)`.

The main statement says, for a finite module `M` over the completion `Â` of a Noetherian
ring `A` along `I`, that `M/IM` is a finite `A/I`-module, and that the classes in
`gr^0_I(M) = M/IM` of any family spanning `M/IM` generate the associated graded module
`gr_I(M)` over `gr_I(A)`: in every degree `n`, the map
`(gr^n_I(A))^t → gr^n_I(M)`, `b ↦ ∑ j, b j • x̄ j` is surjective.
-/

@[expose] public section

universe u v

open scoped BigOperators

namespace Ideal

variable {A : Type u} [CommRing A] (J : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]

/-- The degree `n` piece `J^n M / J^(n+1) M` of the associated graded module
`gr_J(M) = ⨁ n, J^n M / J^(n+1) M`. -/
abbrev associatedGradedModulePiece (n : ℕ) : Type v :=
  (J ^ n • ⊤ : Submodule A M) ⧸
    Submodule.comap (J ^ n • ⊤ : Submodule A M).subtype (J ^ (n + 1) • ⊤)

/-- The bilinear map `J^n × J^m M → J^(n+m) M / J^(n+m+1) M`, `(a, x) ↦ a • x`. -/
def associatedGradedSMulAux (n m : ℕ) :
    (J ^ n : Ideal A) →ₗ[A] (J ^ m • ⊤ : Submodule A M) →ₗ[A]
      associatedGradedModulePiece J M (n + m) :=
  LinearMap.mk₂ A
    (fun a x => Submodule.Quotient.mk
      (⟨a.1 • x.1, by
        rw [pow_add, Submodule.mul_smul]
        exact Submodule.smul_mem_smul a.2 x.2⟩ : (J ^ (n + m) • ⊤ : Submodule A M)))
    (fun a a' x => by
      rw [← Submodule.Quotient.mk_add]
      congr 1
      ext
      simp [add_smul])
    (fun r a x => by
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      ext
      simp [mul_smul])
    (fun a x x' => by
      rw [← Submodule.Quotient.mk_add]
      congr 1
      ext
      simp)
    (fun r a x => by
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      ext
      simp [smul_comm r a.1])

/-- Changing the representative in `J^n` by an element of `J^(n+1)` does not change the
class of `a • x` in `J^(n+m) M / J^(n+m+1) M`. -/
theorem associatedGradedSMulAux_left (n m : ℕ) :
    Submodule.comap (J ^ n).subtype (J ^ (n + 1)) ≤
      (associatedGradedSMulAux J M n m).ker := by
  intro a ha
  ext x
  simp only [LinearMap.zero_apply, associatedGradedSMulAux, LinearMap.mk₂_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
  rw [add_right_comm, pow_add, Submodule.mul_smul]
  exact Submodule.smul_mem_smul ha x.2

/-- Changing the representative in `J^m M` by an element of `J^(m+1) M` does not change
the class of `a • x` in `J^(n+m) M / J^(n+m+1) M`. -/
theorem associatedGradedSMulAux_right (n m : ℕ) :
    Submodule.comap (J ^ m • ⊤ : Submodule A M).subtype (J ^ (m + 1) • ⊤) ≤
      (associatedGradedSMulAux J M n m).flip.ker := by
  intro x hx
  ext a
  simp only [LinearMap.zero_apply, LinearMap.flip_apply, associatedGradedSMulAux,
    LinearMap.mk₂_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.subtype_apply]
  rw [add_assoc, pow_add, Submodule.mul_smul]
  exact Submodule.smul_mem_smul a.2 hx

/-- The scalar multiplication `gr^n_J(A) × gr^m_J(M) → gr^(n+m)_J(M)` of the associated
graded module over the associated graded ring, induced by `(a, x) ↦ a • x` on
representatives `a ∈ J^n`, `x ∈ J^m M`. -/
def associatedGradedSMul (n m : ℕ) :
    associatedGradedPiece J n →ₗ[A] associatedGradedModulePiece J M m →ₗ[A]
      associatedGradedModulePiece J M (n + m) :=
  (associatedGradedSMulAux J M n m).liftQ₂ _ _
    (associatedGradedSMulAux_left J M n m) (associatedGradedSMulAux_right J M n m)

/-- The class in `gr^0_J(M) = M / J M` of an element of `M`. -/
def associatedGradedModuleOf (x : M) : associatedGradedModulePiece J M 0 :=
  Submodule.Quotient.mk ⟨x, by simp⟩

end Ideal

namespace AdicCompletion

/-- (blueprint: lem-weil-pbc-completed-module-associated-graded-generators)
Stacks Project, Lemma 087Z, affine assertion in the proof: for a finite module `M` over
`AdicCompletion I A`, the quotient `M/IM` is finite over `A/I`, and its generators in
degree zero generate the associated graded module `gr_I(M)` over `gr_I(A)`. The first
assertion is `Module.Finite (A ⧸ I) (M ⧸ I • ⊤)`. The second says that for every finite
family `x` of elements of `M` whose classes span `M ⧸ I • ⊤` over `A ⧸ I`, and every
degree `n`, the map `(gr^n_I(A))^t → gr^n_I(M)`, `b ↦ ∑ j, b j • x̄ j` is surjective,
where `x̄ j` is the class of `x j` in `gr^0_I(M)`.

Proof:
1. Noetherianity makes `I` finitely generated. By
   `lem-weil-pbc-adic-completion-mod-ideal` (Stacks 05GG), every element of the completion
   is congruent to an element of `A` modulo the extended ideal `I Â`, and `(I Â) M ⊆ I M`.
   Thus the images of finitely many completion-module generators generate `M/IM` over `A`,
   hence over `A/I`.
2. Generation of the quotient says `M = span(x) + IM`. Hence an element `r • m` with
   `r ∈ I^n` is `∑ j, (r c_j) • x j` modulo `I^(n+1) M`, i.e. its class in `gr^n_I(M)` is
   `∑ j, [r c_j] • x̄ j`. Such elements generate `I^n M`, and the image is additive. -/
theorem completedModule_associatedGraded_generators
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module (AdicCompletion I A) M]
    [Module.Finite (AdicCompletion I A) M] :
    letI : Module A M := Module.compHom M (algebraMap A (AdicCompletion I A))
    Module.Finite (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M)) ∧
    ∀ (t : ℕ) (x : Fin t → M),
      Submodule.span (A ⧸ I)
          (Set.range fun j => Submodule.Quotient.mk (p := (I • ⊤ : Submodule A M)) (x j)) =
        ⊤ →
      ∀ n : ℕ, Function.Surjective fun b : Fin t → I.associatedGradedPiece n =>
        ∑ j, I.associatedGradedSMul M n 0 (b j) (I.associatedGradedModuleOf M (x j)) := by
  classical
  let _ : Module A M := Module.compHom M (algebraMap A (AdicCompletion I A))
  refine ⟨?_, ?_⟩
  · -- the extended ideal `I Â` maps `M` into `I M`
    have hext (e : AdicCompletion I A) (he : e ∈ I.map (algebraMap A (AdicCompletion I A)))
        (m : M) : e • m ∈ (I • ⊤ : Submodule A M) := by
      induction he using Submodule.span_induction generalizing m with
      | mem e he =>
        obtain ⟨i, hi, rfl⟩ := he
        exact Submodule.smul_mem_smul hi trivial
      | zero => simp
      | add e e' _ _ he he' => simpa [add_smul] using add_mem (he m) (he' m)
      | smul d e _ he => simpa [smul_eq_mul, mul_comm d e, mul_smul] using he (d • m)
    -- every element of `Â` is congruent to an element of `A` modulo `I Â`
    have hlift (c : AdicCompletion I A) : ∃ a : A,
        c - algebraMap A (AdicCompletion I A) a ∈ I.map (algebraMap A (AdicCompletion I A)) := by
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalOneₐ I c)
      refine ⟨a, ?_⟩
      rw [← ker_evalOneₐ_eq_map I (IsNoetherian.noetherian I), RingHom.mem_ker]
      simp [← ha]
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := AdicCompletion I A) (M := M)
    suffices Module.Finite A (M ⧸ (I • ⊤ : Submodule A M)) from
      Module.Finite.of_restrictScalars_finite A (A ⧸ I) _
    refine ⟨⟨s.image (Submodule.Quotient.mk (p := (I • ⊤ : Submodule A M))), ?_⟩⟩
    rw [eq_top_iff]
    rintro q -
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hm : m ∈ Submodule.span (AdicCompletion I A) (s : Set M) := hs ▸ trivial
    induction hm using Submodule.span_induction with
    | mem m hm => exact Submodule.subset_span (by simpa using ⟨m, hm, rfl⟩)
    | zero => simp
    | add m m' _ _ h h' => simpa using add_mem h h'
    | smul c m _ h =>
      obtain ⟨a, ha⟩ := hlift c
      have : Submodule.Quotient.mk (p := (I • ⊤ : Submodule A M)) (c • m) =
          a • Submodule.Quotient.mk m := by
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
        have h := hext _ ha m
        rw [sub_smul] at h
        exact h
      rw [this]
      exact Submodule.smul_mem _ a h
  · intro t x hx n q
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    induction hy using Submodule.smul_induction_on' with
    | smul r hr m _ =>
      obtain ⟨cbar, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (A ⧸ I)).1
        (hx ▸ Submodule.mem_top (x := Submodule.Quotient.mk (p := (I • ⊤ : Submodule A M)) m))
      choose c hc' using fun j => Ideal.Quotient.mk_surjective (cbar j)
      refine ⟨fun j => Submodule.Quotient.mk ⟨r * c j, Ideal.mul_mem_right _ _ hr⟩, ?_⟩
      simp only [Ideal.associatedGradedSMul, Ideal.associatedGradedModuleOf,
        LinearMap.liftQ₂_mk, Ideal.associatedGradedSMulAux, LinearMap.mk₂_apply]
      simp only [← Submodule.mkQ_apply, ← map_sum]
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      have hm : ∑ j, c j • x j - m ∈ (I • ⊤ : Submodule A M) := by
        rw [← Submodule.Quotient.eq, ← hc, ← Submodule.mkQ_apply, map_sum]
        simp [← hc']
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
        Submodule.coe_sum, mul_smul, ← Finset.smul_sum, ← smul_sub]
      rw [pow_succ, Submodule.mul_smul]
      exact Submodule.smul_mem_smul hr hm
    | add y hy z hz hy' hz' =>
      obtain ⟨b, hb⟩ := hy'
      obtain ⟨b', hb'⟩ := hz'
      refine ⟨b + b', ?_⟩
      simp only [Pi.add_apply, map_add, LinearMap.add_apply, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) hb hb'

end AdicCompletion
