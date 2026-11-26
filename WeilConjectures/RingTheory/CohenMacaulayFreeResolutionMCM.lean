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
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.CohenMacaulayDepthFirstTerm

/-!
# Maximal Cohen–Macaulay syzygies

Over a Noetherian local Cohen–Macaulay ring of dimension `d`, the left term of a finite free
exact sequence of length `d - e` ending in a finite module of depth `e` is zero or maximal
Cohen–Macaulay.

## Implementation details

Splitting the sequence into short exact sequences, the depth of the syzygies grows by one at each
step up to `d` (`first_term_depth_ge`); the reverse bound comes from `depth_le_supportDim`.

## References

* [Stacks, Tag 00NG]
* [Stacks, Tag 00NE]
* [Stacks, Tag 00LX]
* [Stacks, Tag 00LK]
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits

namespace IsLocalRing

/-- Let `R` be a Noetherian local ring of dimension `d` and depth at least `d`, and let `M` be a
nonzero finite module of depth `e ≤ d`. If `0 → K → F_{d-e-1} → ⋯ → F_0 → M → 0` is exact with
the `F_i` finite free, then `K` is finite and either zero or of depth `d`. -/
theorem first_term_is_maximalCohenMacaulay
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (d e : ℕ) (hdim : ringKrullDim R = (d : WithBot ℕ∞))
    (hcm : (d : ℕ∞) ≤ depth (R := R) R)
    (he : depth (R := R) M = (e : ℕ∞)) (hed : e ≤ d)
    (S : ComposableArrows (ModuleCat.{max u v} R) (d - e + 3))
    (hS : S.Exact) (hzero0 : IsZero (S.obj' 0))
    (hzero1 : IsZero (S.obj' (d - e + 3)))
    (hM : Nonempty ((S.obj' (d - e + 2)) ≃ₗ[R] M))
    (hfree : ∀ i : Fin (d - e),
      Module.Free R (S.obj' (i.val + 2) (by omega)) ∧
      Module.Finite R (S.obj' (i.val + 2) (by omega))) :
    (let K := S.obj' 1
     ∃ hK : Module.Finite R K,
       letI := hK
       Subsingleton K ∨ depth (R := R) K = (d : ℕ∞)) := by
  dsimp
  have h1 : 1 ≤ d - e + 3 := by omega
  have hfinite2 : Module.Finite R (S.obj' 2) := by
    by_cases hn : d - e = 0
    · obtain ⟨a⟩ := hM
      have hfinite := Module.Finite.equiv a.symm
      have hobj : S.obj' (d - e + 2) = S.obj' 2 := by
        congr 1
        omega
      rw [hobj] at hfinite
      exact hfinite
    · exact (hfree ⟨0, by omega⟩).2
  have hmono : Mono (S.map' 1 2) :=
    (hS.exact 0).mono_g (hzero0.eq_of_src _ _)
  have hK : Module.Finite R (S.obj' 1) :=
    Module.Finite.of_injective (S.map' 1 2).hom
      ((ModuleCat.mono_iff_injective _).mp hmono)
  refine ⟨hK, ?_⟩
  rcases subsingleton_or_nontrivial (S.obj' 1) with hzero | hnonzero
  · exact Or.inl hzero
  · have hlower := first_term_depth_ge M d e hcm he hed S hS hzero0 hzero1 hM hfree
    have hupper : (depth (R := R) (S.obj' 1 h1) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
      calc
        _ ≤ Module.supportDim R (S.obj' 1 h1) := depth_le_supportDim (S.obj' 1 h1)
        _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R (S.obj' 1 h1)
        _ = _ := hdim
    exact Or.inr (le_antisymm (WithBot.coe_le_coe.mp hupper) hlower)

end IsLocalRing
