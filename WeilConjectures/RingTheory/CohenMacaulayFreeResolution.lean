/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ExactSequence
import WeilConjectures.RingTheory.DepthLeSupportDimension
import WeilConjectures.RingTheory.CohenMacaulayFreeResolutionConstruction
import WeilConjectures.RingTheory.CohenMacaulayFreeResolutionMCM

/-!
# Finite free resolutions ending in maximal Cohen–Macaulay modules

Over a Noetherian local Cohen–Macaulay ring of dimension `d`, a nonzero finite module `M` of
depth `e` has a finite free resolution of length `d - e` ending in a module that is zero or
maximal Cohen–Macaulay.

## Implementation details

Depth is bounded by support dimension, so `e ≤ d`. The proof is by induction on `d - e`: the
kernel of a finite free surjection onto a module of depth below `d` has depth one larger, and
the induction hypothesis is spliced with this presentation. The linear equivalence identifies
the penultimate object with `M` even when `R` and `M` have different universes.

## References

* [Stacks, Tag 00NG]
* [Stacks, Tag 00NE]
* [Stacks, Tag 00NF]
* [Stacks, Tag 00LK]
* [Stacks, Tag 00LX]
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace IsLocalRing

/-- Over a Noetherian local Cohen–Macaulay ring of dimension `d`, a nonzero finite module
has depth `e ≤ d` and an exact sequence `0 → K → F_{d-e-1} → ⋯ → F₀ → M → 0`,
with the `Fᵢ` finite free and `K` finite and either zero or of depth `d`.
For `k = d - e`, the objects of `S` in order are `0, K, F_{k-1}, …, F₀, M, 0`. -/
theorem exists_finite_free_resolution_to_maximalCohenMacaulay
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (d : ℕ) (hdim : ringKrullDim R = (d : WithBot ℕ∞))
    (hcm : (d : ℕ∞) ≤ depth (R := R) R) :
    ∃ e : ℕ, depth (R := R) M = (e : ℕ∞) ∧ e ≤ d ∧
      ∃ S : ComposableArrows (ModuleCat.{max u v} R) (d - e + 3),
        S.Exact ∧ IsZero (S.obj' 0) ∧ IsZero (S.obj' (d - e + 3)) ∧
        Nonempty ((S.obj' (d - e + 2)) ≃ₗ[R] M) ∧
        (∀ i : Fin (d - e),
          Module.Free R (S.obj' (i.val + 2) (by omega)) ∧
          Module.Finite R (S.obj' (i.val + 2) (by omega))) ∧
        (let K := S.obj' 1
         ∃ hK : Module.Finite R K,
           letI := hK
           Subsingleton K ∨ depth (R := R) K = (d : ℕ∞)) := by
  have hbound : (depth (R := R) M : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
    calc
      (depth (R := R) M : WithBot ℕ∞) ≤ Module.supportDim R M := depth_le_supportDim M
      _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R M
      _ = (d : WithBot ℕ∞) := hdim
  have hle : depth (R := R) M ≤ (d : ℕ∞) := WithBot.coe_le_coe.mp hbound
  have hfinite : depth (R := R) M ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) hle
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hed : e ≤ d := ENat.natCast_le_natCast.mp (he ▸ hle)
  obtain ⟨S, hS, h0, hlast, hM, hfree⟩ :=
    exists_finite_free_resolution_data (R := R) M (d - e)
  refine ⟨e, he.symm, hed, S, hS, h0, hlast, hM, hfree, ?_⟩
  exact first_term_is_maximalCohenMacaulay M d e hdim hcm he.symm hed
    S hS h0 hlast hM hfree

end IsLocalRing
