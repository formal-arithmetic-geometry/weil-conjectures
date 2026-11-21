/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.PreciseVanishingCore
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Precise vanishing for truncated bounded projective complexes

## References

* Stacks Project, Tag 064D
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive

universe u v w

namespace CategoryTheory

/-- Precise vanishing for maps from a truncated bounded projective complex. -/
theorem precise_vanishing
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P K : CochainComplex A ℤ) (n : ℤ)
    (hPbounded : ∃ a b : ℤ,
      (∀ i : ℤ, i < a → IsZero (P.X i)) ∧
      (∀ i : ℤ, b < i → IsZero (P.X i)))
    (hPprojective : ∀ i : ℤ, Projective (P.X i))
    (hPtruncated : ∀ i : ℤ, i < n → IsZero (P.X i))
    (hKvanishing : ∀ i : ℤ, n ≤ i → IsZero (K.homology i)) :
    ∀ f : (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj K), f = 0 := by
  have : K.IsLE (n - 1) := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hKvanishing i (by omega)
  have hz : ∀ f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (K.truncLE (n - 1)),
      f = 0 := by
    apply precise_vanishing_of_homotopy_zero A P (K.truncLE (n - 1))
      hPbounded hPprojective
    intro g
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective g
    have hg : g = 0 := by
      ext i
      by_cases hi : i < n
      · exact (hPtruncated i hi).eq_of_src _ _
      · exact ((K.truncLE (n - 1)).isZero_of_isStrictlyLE (n - 1) i
          (by omega)).eq_of_tgt _ _
    simp [hg]
  intro f
  have : IsIso (DerivedCategory.Q.map (K.ιTruncLE (n - 1))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso A _).2 inferInstance
  have h := hz (f ≫ inv (DerivedCategory.Q.map (K.ιTruncLE (n - 1))))
  simpa using congrArg (fun g ↦ g ≫ DerivedCategory.Q.map (K.ιTruncLE (n - 1))) h

end CategoryTheory
