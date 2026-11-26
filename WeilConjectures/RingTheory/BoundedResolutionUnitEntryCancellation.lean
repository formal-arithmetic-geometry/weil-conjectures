/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.Algebra.Homology.NatUnitEntryHomotopyCancellation
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.FiniteType

/-!
# Cancellation at a supplied unit entry in a bounded free resolution

Given a bounded finite free resolution with chosen bases and a unit entry of the differential
`d_{j+1}`, we cancel the corresponding pair of basis vectors to obtain a bounded finite free
resolution of the same module whose ranks do not increase and whose rank in degree `j` drops
(`ModuleCat.exists_bounded_resolution_unit_entry_cancellation`).

## Implementation details

The new complex comes from the natural-degree homotopy cancellation theorem, which supplies a
smaller complex with finite bases and a homotopy equivalence whose forward map is degreewise
injective; injectivity gives boundedness. The hypothesis `j < d` is kept in the statement,
although the argument does not need it. The unit pivot is an input, not chosen.

## References

* [Stacks, Tag 00MT]
* [Stacks, Tag 00OA]
-/

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat

/-- Cancelling a supplied unit entry of the differential `d_{j+1}` of a bounded finite free
resolution `P` of `M` gives a bounded finite free resolution of `M` with ranks at most those of
`P` and strictly smaller rank in degree `j`. -/
theorem exists_bounded_resolution_unit_entry_cancellation {R : Type u} [CommRing R]
    [Nontrivial R] (M : ModuleCat.{max u v} R) (d : ℕ) (P : ProjectiveResolution M)
    (hzero : ∀ i : ℕ, d < i → IsZero (P.complex.X i))
    (n : ℕ → ℕ) (b : ∀ i : ℕ, Module.Basis (Fin (n i)) R (P.complex.X i))
    (j : ℕ) (hjd : j < d) (p : Fin (n (j + 1))) (q : Fin (n j))
    (hu : IsUnit (LinearMap.toMatrix (b (j + 1)) (b j)
      (P.complex.d (j + 1) j).hom q p)) :
    ∃ P' : ProjectiveResolution M,
      (∀ i : ℕ, d < i → IsZero (P'.complex.X i)) ∧
      (∀ i : ℕ, Module.Finite R (P'.complex.X i) ∧ Module.Free R (P'.complex.X i)) ∧
      (∀ i : Fin (d + 1), Module.finrank R (P'.complex.X i.val) ≤
        Module.finrank R (P.complex.X i.val)) ∧
      Module.finrank R (P'.complex.X j) < Module.finrank R (P.complex.X j) := by
  have _ := hjd
  obtain ⟨C', n', e, hb', hinj, hsucc, hj, hother⟩ :=
    ChainComplex.exists_nat_homotopy_cancellation_of_isUnit_entry P.complex n b j p q hu
  let b' : ∀ i : ℕ, Module.Basis (Fin (n' i)) R (C'.X i) :=
    fun i ↦ (hb' i).some
  let P' : ProjectiveResolution M :=
    { complex := C'
      projective := fun i ↦ ModuleCat.projective_of_free (b' i)
      π := e.hom ≫ P.π }
  have hrank : ∀ i, Module.finrank R (P.complex.X i) = n i := by
    intro i
    simpa using Module.finrank_eq_card_basis (b i)
  have hrank' : ∀ i, Module.finrank R (P'.complex.X i) = n' i := by
    intro i
    simpa using Module.finrank_eq_card_basis (b' i)
  refine ⟨P', ?_, ?_, ?_, ?_⟩
  · intro i hi
    apply ModuleCat.isZero_iff_subsingleton.mpr
    have : Subsingleton (P.complex.X i) :=
      ModuleCat.isZero_iff_subsingleton.mp (hzero i hi)
    exact (hinj i).subsingleton
  · intro i
    exact ⟨Module.Finite.of_basis (b' i), Module.Free.of_basis (b' i)⟩
  · intro i
    rw [hrank', hrank]
    by_cases hs : i.val = j + 1
    · rw [hs]
      omega
    by_cases ht : i.val = j
    · rw [ht]
      omega
    rw [hother i.val hs ht]
  · rw [hrank', hrank]
    omega

end ModuleCat
