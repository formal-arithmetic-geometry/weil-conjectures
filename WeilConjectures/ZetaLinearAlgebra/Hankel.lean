/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Pi
public import WeilConjectures.Mathlib.LinearAlgebra.Determinant
public import WeilConjectures.ZetaLinearAlgebra.ShiftSpan

@[expose] public section

/-!
# Rationality of a power series descends along a field extension

Let `K ⊆ L` be fields. A power series `f ∈ K⟦X⟧` which becomes rational over `L`, in the
sense that it admits a normalized fraction `A / B` with `A B : L[X]` and `B.coeff 0 = 1`,
already admits one with `A B : K[X]`.

The proof is linear algebra: by `WeilConjectures.ZetaLinearAlgebra.ShiftSpan`, rationality of
`f` is equivalent to finite-dimensionality of the span of the shifts of its coefficient
sequence, and such a span cannot shrink when the field of coefficients is enlarged, because
linear independence of finitely many sequences is witnessed by a nonvanishing determinant
(`LinearIndependent.map_algebraMap`).

## Main statements

- `algebraMap_comp_mem_shiftSpan`: pushing a sequence along a field extension maps its shift
  span into the shift span of the pushed sequence.
- `finiteDimensional_shiftSpan_of_map` and `finrank_shiftSpan_le_finrank_shiftSpan_map`: the
  shift span of a sequence does not shrink when the coefficients are pushed to a larger field.
- `PowerSeries.exists_normalized_fraction_of_map`: a power series over `K` that is rational
  over an extension field `L` is rational over `K`.
- `PowerSeries.exists_normalized_fraction_of_map_rat`: the case `K = ℚ`, which is what the
  rationality of the zeta function needs.
-/

open Finset

open scoped Polynomial PowerSeries

section ShiftSpan

variable {K : Type*} (L : Type*) [Field K] [Field L] [Algebra K L]

/-- Pushing the values of a sequence along a field extension maps the shift span into the
shift span. -/
lemma algebraMap_comp_mem_shiftSpan {a x : ℕ → K} (hx : x ∈ shiftSpan K a) :
    algebraMap K L ∘ x ∈ shiftSpan L (algebraMap K L ∘ a) := by
  have h : Submodule.span K (Set.range fun m : ℕ => (⇑(seqShift K))^[m] a) ≤
      Submodule.comap ((Algebra.linearMap K L).compLeft ℕ)
        ((shiftSpan L (algebraMap K L ∘ a)).restrictScalars K) := by
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    have heq : (Algebra.linearMap K L).compLeft ℕ ((⇑(seqShift K))^[m] a)
        = (⇑(seqShift L))^[m] (algebraMap K L ∘ a) := by
      funext n
      simp [LinearMap.compLeft, iterate_seqShift_apply]
    simp only [SetLike.mem_coe, Submodule.mem_comap, Submodule.restrictScalars_mem, heq]
    exact iterate_seqShift_mem_shiftSpan (algebraMap K L ∘ a) m
  exact h hx

/-- The shift span over the base field is at most as large as the shift span of the pushed
sequence over the extension field. -/
theorem rank_shiftSpan_le_finrank_shiftSpan_map (a : ℕ → K)
    [FiniteDimensional L (shiftSpan L (algebraMap K L ∘ a))] :
    Module.rank K (shiftSpan K a)
      ≤ (Module.finrank L (shiftSpan L (algebraMap K L ∘ a)) : Cardinal) := by
  refine rank_le fun s hs => ?_
  set e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin (s : Type _)).symm
  have hu : LinearIndependent K fun i => ((e i : shiftSpan K a) : ℕ → K) :=
    (hs.comp e e.injective).map' (shiftSpan K a).subtype (Submodule.ker_subtype _)
  have hmem : ∀ i, algebraMap K L ∘ ((e i : shiftSpan K a) : ℕ → K)
      ∈ shiftSpan L (algebraMap K L ∘ a) := fun i => algebraMap_comp_mem_shiftSpan L (e i).1.2
  have hw : LinearIndependent L fun i => (⟨_, hmem i⟩ : shiftSpan L (algebraMap K L ∘ a)) :=
    LinearIndependent.of_comp (shiftSpan L (algebraMap K L ∘ a)).subtype hu.map_algebraMap
  simpa [Fintype.card_coe] using hw.fintype_card_le_finrank

/-- Hankel descent for shift spans: if the shift span of the pushed sequence is
finite-dimensional over the extension field, then the shift span of the original sequence is
finite-dimensional over the base field. -/
theorem finiteDimensional_shiftSpan_of_map (a : ℕ → K)
    (h : FiniteDimensional L (shiftSpan L (algebraMap K L ∘ a))) :
    FiniteDimensional K (shiftSpan K a) :=
  have := h
  Module.rank_lt_aleph0_iff.mp <|
    lt_of_le_of_lt (rank_shiftSpan_le_finrank_shiftSpan_map L a) Cardinal.natCast_lt_aleph0

/-- The dimension of the shift span does not decrease when the coefficients are pushed to a
larger field. -/
theorem finrank_shiftSpan_le_finrank_shiftSpan_map (a : ℕ → K)
    (h : FiniteDimensional L (shiftSpan L (algebraMap K L ∘ a))) :
    Module.finrank K (shiftSpan K a) ≤ Module.finrank L (shiftSpan L (algebraMap K L ∘ a)) :=
  have := h
  Module.finrank_le_of_rank_le (rank_shiftSpan_le_finrank_shiftSpan_map L a)

end ShiftSpan

namespace PowerSeries

variable {K : Type*} (L : Type*) [Field K] [Field L] [Algebra K L]

/-- Hankel rationality descent: a power series over `K` which admits a normalized fraction
over an extension field `L` admits one over `K`. -/
theorem exists_normalized_fraction_of_map (f : K⟦X⟧)
    (h : ∃ A B : L[X], B.coeff 0 = 1 ∧
      map (algebraMap K L) f * (B : L⟦X⟧) = (A : L⟦X⟧)) :
    ∃ A B : K[X], B.coeff 0 = 1 ∧ f * (B : K⟦X⟧) = (A : K⟦X⟧) := by
  rw [exists_normalized_fraction_iff_finiteDimensional_shiftSpan] at h ⊢
  have hcoeff : (fun n => coeff n (map (algebraMap K L) f))
      = algebraMap K L ∘ fun n => coeff n f := by
    funext n
    simp
  rw [hcoeff] at h
  exact finiteDimensional_shiftSpan_of_map L _ h

/-- Hankel rationality descent over the rationals: a power series with rational coefficients
which admits a normalized fraction over a field extension of `ℚ` admits one over `ℚ`. This is
the form the rationality of the zeta function uses. -/
theorem exists_normalized_fraction_of_map_rat [Algebra ℚ L] (f : ℚ⟦X⟧)
    (h : ∃ A B : L[X], B.coeff 0 = 1 ∧
      map (algebraMap ℚ L) f * (B : L⟦X⟧) = (A : L⟦X⟧)) :
    ∃ A B : ℚ[X], B.coeff 0 = 1 ∧ f * (B : ℚ⟦X⟧) = (A : ℚ⟦X⟧) :=
  exists_normalized_fraction_of_map L f h

end PowerSeries
