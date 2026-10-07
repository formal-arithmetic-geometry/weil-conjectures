/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Artinian.Ring

/-!
# Connected reduced finite algebras over an algebraically closed field

A finite reduced algebra `B` over an algebraically closed field `K` whose only idempotents are
`0` and `1` is `K` itself: `B` is Artinian and reduced, hence a finite product of fields, and
having no nontrivial idempotents it is a single field, finite over `K`, hence equal to `K`.

## Main statements

- `IsAlgClosed.finrank_eq_one_of_isReduced`: such an algebra has `finrank K B = 1`.
-/

@[expose] public section

/-- A nontrivial finite reduced algebra `B` over an algebraically closed field `K` whose only
idempotents are `0` and `1` has dimension `1` over `K`. This is the algebraic step of Stacks
0BUG (`Γ(X, 𝒪_X) = k` for `X` proper, geometrically connected and geometrically reduced). -/
theorem IsAlgClosed.finrank_eq_one_of_isReduced {K B : Type*} [Field K] [IsAlgClosed K]
    [CommRing B] [Algebra K B] [Module.Finite K B] [IsReduced B] [Nontrivial B]
    (hB : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : Module.finrank K B = 1 := by
  have : IsArtinianRing B := IsArtinianRing.of_finite K B
  have : Subsingleton (MaximalSpectrum B) := by
    refine ⟨fun I J ↦ by_contra fun hIJ ↦ ?_⟩
    classical
    let e := (IsArtinianRing.equivPi B).symm (Pi.single I 1)
    have he : IsIdempotentElem e := by
      simp only [IsIdempotentElem, e, ← map_mul, ← Pi.single_mul, one_mul]
    rcases hB e he with h | h
    · have := congr_fun ((IsArtinianRing.equivPi B).symm.injective (h.trans (map_zero _).symm)) I
      simp at this
    · have := congr_fun ((IsArtinianRing.equivPi B).symm.injective (h.trans (map_one _).symm)) J
      simp [Ne.symm hIJ] at this
  have : IsLocalRing B := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal B
    refine IsLocalRing.of_unique_max_ideal ⟨m, hm, fun n hn ↦ ?_⟩
    exact congrArg MaximalSpectrum.asIdeal (Subsingleton.elim (⟨n, hn⟩ : MaximalSpectrum B) ⟨m, hm⟩)
  have := (IsArtinianRing.isField_of_isReduced_of_isLocalRing B).isDomain
  exact ((LinearEquiv.ofBijective (Algebra.linearMap K B)
    IsAlgClosed.algebraMap_bijective_of_isIntegral).finrank_eq.symm).trans
    (Module.finrank_self K)
