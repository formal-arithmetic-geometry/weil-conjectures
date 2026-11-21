/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The rank of a matrix is unchanged by field extension

Source: Milne, Lectures on Étale Cohomology, Chapter II, §27, proof of Lemma 27.9, last sentence;
Deligne, La conjecture de Weil I, "Preuve de (1.7) ⇒ (1.6)".
-/

@[expose] public section

universe u v

namespace Matrix

/-- Let `ι : K →+* L` be a ring homomorphism
of fields and `A` an `m × n` matrix with entries in `K`, viewed over `L` by applying `ι` to
every entry (`A.map ι`). The rank (the dimension of the span of the rows,
`Matrix.rank_eq_finrank_span_row`) is the same over `L` and over `K`; equivalently, a family
of rows of `A` is linearly independent over `L` if and only if it is over `K`. Source: Milne,
LEC, §27, proof of Lemma 27.9; Deligne, Weil I, proof of (1.7) ⇒ (1.6). -/
theorem rank_map_field_extension {K : Type u} {L : Type v} [Field K] [Field L] (ι : K →+* L)
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) :
    (A.map ι).rank = A.rank ∧
      ∀ s : Set (Fin m), LinearIndependent L (fun i : s ↦ (A.map ι).row i) ↔
        LinearIndependent K (fun i : s ↦ A.row i) := by
  let _ : Algebra K L := ι.toAlgebra
  have hι : Function.Injective ι := (RingHom.injective ι)
  have hind : ∀ s : Set (Fin m), LinearIndependent L (fun i : s ↦ (A.map ι).row i) ↔
      LinearIndependent K (fun i : s ↦ A.row i) := by
    intro s
    rw [show (fun i : s ↦ (A.map ι).row i) =
        (fun i : s ↦ ι ∘ A.row i) by
      funext i; funext j; rfl]
    simpa [RingHom.algebraMap_toAlgebra] using
      (linearIndependent_algebraMap_comp_iff (R := K) (S := L)
        (ι := s) (ι' := Fin n) (v := fun i : s ↦ A.row i))
  have hrank : ∀ r : ℕ, r ≤ (A.map ι).rank ↔ r ≤ A.rank := by
    intro r
    have hmap := le_rank_map_iff A ι r
    have hid := le_rank_map_iff A (RingHom.id K) r
    rw [hmap]
    have hid' : r ≤ A.rank ↔ ∃ (e₁ : Fin r → Fin m) (e₂ : Fin r → Fin n),
        (A.submatrix e₁ e₂).det ≠ 0 := by simpa using hid
    constructor
    · rintro ⟨e₁, e₂, h⟩
      exact hid'.mpr ⟨e₁, e₂, fun hz => h (by rw [hz, map_zero])⟩
    · intro h
      obtain ⟨e₁, e₂, h⟩ := hid'.mp h
      refine ⟨e₁, e₂, ?_⟩
      intro hz
      apply h
      apply hι
      simpa using hz
  refine ⟨le_antisymm (hrank _ |>.mp le_rfl) (hrank _ |>.mpr le_rfl), hind⟩

end Matrix
