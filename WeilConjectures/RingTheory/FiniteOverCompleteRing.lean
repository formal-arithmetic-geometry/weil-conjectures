/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite modules over adically complete rings

A Hausdorff module over an adically complete ring is finite as soon as its reduction modulo
the ideal is finite, and lifts of generators of the reduction generate the module.

## Main results

- `Module.finite_and_span_eq_top_of_adicComplete`

## References

- Stacks Project, Algebra, Lemma 10.96.12 (Tag 031D).
-/

@[expose] public section

universe u v

namespace Module

private theorem mem_smul_top_pi_iff {A : Type u} [CommRing A] (J : Ideal A)
    {r : ℕ} (a : Fin r → A) :
    a ∈ (J • ⊤ : Submodule A (Fin r → A)) ↔ ∀ j, a j ∈ J := by
  classical
  constructor
  · intro ha j
    have h := Submodule.smul_top_le_comap_smul_top J (LinearMap.proj j) ha
    simpa using h
  · intro ha
    have heq : a = ∑ j, a j • Pi.single j (1 : A) := by
      ext j
      simp [Pi.single_apply]
    rw [heq]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem_smul (ha j) Submodule.mem_top

private theorem precomplete_fin {A : Type u} [CommRing A] (I : Ideal A)
    [IsPrecomplete I A] (r : ℕ) : IsPrecomplete I (Fin r → A) := by
  classical
  constructor
  intro f hf
  have hc (j : Fin r) : ∃ L : A, ∀ n, f n j ≡ L [SMOD (I ^ n • ⊤ : Submodule A A)] := by
    apply IsPrecomplete.prec' (I := I)
    intro m n hmn
    have h := (mem_smul_top_pi_iff (I ^ m) (f m - f n)).mp
      (SModEq.sub_mem.mp (hf hmn)) j
    simpa [SModEq.sub_mem] using h
  choose L hL using hc
  refine ⟨L, fun n ↦ SModEq.sub_mem.mpr ?_⟩
  apply (mem_smul_top_pi_iff (I ^ n) _).mpr
  intro j
  simpa [SModEq.sub_mem] using hL j n

/-- A Hausdorff module `M` over an `I`-adically complete ring `A` is finite if `M / IM` is
finite over `A / I`; moreover, every finite family whose images generate `M / IM` generates
`M`. -/
theorem finite_and_span_eq_top_of_adicComplete
    {A : Type u} [CommRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M]
    [IsAdicComplete I A] [IsHausdorff I M]
    [Module.Finite (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M))] :
    Module.Finite A M ∧
      ∀ (r : ℕ) (x : Fin r → M),
        Submodule.span (A ⧸ I)
          (Set.range (fun j ↦ (I • (⊤ : Submodule A M)).mkQ (x j))) = ⊤ →
        Submodule.span A (Set.range x) = ⊤ := by
  classical
  have hspan : ∀ (r : ℕ) (x : Fin r → M),
      Submodule.span (A ⧸ I)
        (Set.range (fun j ↦ (I • (⊤ : Submodule A M)).mkQ (x j))) = ⊤ →
      Submodule.span A (Set.range x) = ⊤ := by
    intro r x hx
    have : IsPrecomplete I (Fin r → A) := precomplete_fin I r
    apply (span_range_eq_top_iff_surjective_fintypeLinearCombination A x).mpr
    apply surjective_of_mkQ_comp_surjective (I := I)
    intro y
    obtain ⟨c, hc⟩ :=
      (span_range_eq_top_iff_surjective_fintypeLinearCombination (A ⧸ I) _).mp hx y
    choose a ha using fun j ↦ Ideal.Quotient.mk_surjective (c j)
    refine ⟨a, ?_⟩
    change (I • (⊤ : Submodule A M)).mkQ (∑ j, a j • x j) = y
    rw [map_sum]
    simpa only [Fintype.linearCombination_apply, ← ha,
      Module.Quotient.mk_smul_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_smul,
      map_smul] using hc
  refine ⟨?_, hspan⟩
  obtain ⟨r, y, hy⟩ := Module.Finite.exists_fin (R := A ⧸ I)
    (M := M ⧸ (I • ⊤ : Submodule A M))
  choose x hx using fun j ↦ (I • (⊤ : Submodule A M)).mkQ_surjective (y j)
  have hxspan := hspan r x (by simpa only [hx] using hy)
  exact Module.Finite.of_fg_top (hxspan ▸ Submodule.fg_span (Set.finite_range x))

end Module
