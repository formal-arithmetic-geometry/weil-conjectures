/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulDualComplex
public import WeilConjectures.RingTheory.KoszulRegularSequence
import WeilConjectures.RingTheory.KoszulComplementaryEquivalences
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Dual Koszul cohomology below the top degree

The signed dual of the Koszul complex of a Koszul-regular sequence has zero cohomology below
its top degree.

## Implementation details

The complementary-wedge isomorphisms, rescaled degreewise by signs, identify the signed dual
with the reversed Koszul complex, so the cohomology in degree `n < r` is Koszul homology in
degree `r - n > 0`.

## References

* [Stacks, Tag 0BQZ]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ExteriorAlgebra

/-- The signed dual of a Koszul-regular complex has zero cohomology below its top degree. -/
theorem koszulDual_isZero_homology_below_top
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (n : ℕ) (hn : n < r) :
    IsZero ((koszulDualComplex A r f).homology n) := by
  obtain ⟨e, he⟩ := exists_koszul_complementary_equivalences A r f
  apply HomologicalComplex.ExactAt.isZero_homology
  cases n with
  | zero =>
    have hr : r ≠ 0 := by omega
    have hK := ((koszulComplex A r f).exactAt_iff_isZero_homology r).mpr (hreg r hr)
    have hK' : ((koszulComplex A r f).sc' (r + 1) r (r - 1)).Exact :=
      ((koszulComplex A r f).exactAt_iff' (r + 1) r (r - 1)
        (by simp) (by cases r <;> simp_all)).mp hK
    apply ((koszulDualComplex A r f).exactAt_iff' 0 0 1 (by simp) (by simp)).mpr
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    change (koszulDualComplex A r f).X 0 at x
    change (koszulDualComplex A r f).d 0 1 x = 0 at hx
    have hx' : (koszulComplex A r f).d r (r - 1) (e 0 (by omega) x) = 0 := by
      simpa [hx] using (he 0 hn x).symm
    obtain ⟨y, hy⟩ := ((ShortComplex.moduleCat_exact_iff _).mp hK') _ hx'
    change (koszulComplex A r f).X (r + 1) at y
    change (koszulComplex A r f).d (r + 1) r y = e 0 (by omega) x at hy
    have hy0 : y = 0 := by
      classical
      let b := (Finsupp.basisSingleOne : Module.Basis (Fin r) A
        (Fin r →₀ A)).exteriorPower (r + 1)
      have : IsEmpty (Set.powersetCard (Fin r) (r + 1)) := ⟨fun s ↦ by
        have hcard : s.val.card ≤ r := by simpa using Finset.card_le_univ s.val
        have : s.val.card = r + 1 := s.property
        omega⟩
      have : Subsingleton (⋀[A]^(r + 1) (Fin r →₀ A)) := b.repr.injective.subsingleton
      change (y : ⋀[A]^(r + 1) (Fin r →₀ A)) = 0
      exact @Subsingleton.elim (⋀[A]^(r + 1) (Fin r →₀ A)) inferInstance y 0
    have hx0 : x = 0 := by
      apply (e 0 (by omega)).injective
      simpa only [hy0, map_zero] using hy.symm
    exact ⟨0, by simp [hx0]⟩
  | succ n =>
    have hpos : r - (n + 1) ≠ 0 := by omega
    have hK := ((koszulComplex A r f).exactAt_iff_isZero_homology (r - (n + 1))).mpr
      (hreg _ hpos)
    have hK' : ((koszulComplex A r f).sc' (r - n) (r - (n + 1))
        (r - (n + 2))).Exact :=
      ((koszulComplex A r f).exactAt_iff' (r - n) (r - (n + 1)) (r - (n + 2))
        (by simp; omega) (by
          apply (ComplexShape.down ℕ).next_eq'
          change r - (n + 2) + 1 = r - (n + 1)
          omega)).mp hK
    apply ((koszulDualComplex A r f).exactAt_iff' n (n + 1) (n + 2)
      (by simp) (by simp)).mpr
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    change (koszulDualComplex A r f).X (n + 1) at x
    change (koszulDualComplex A r f).d (n + 1) (n + 2) x = 0 at hx
    have hx' : (koszulComplex A r f).d (r - (n + 1)) (r - (n + 2))
        (e (n + 1) (by omega) x) = 0 := by
      simpa only [Nat.add_assoc, hx, map_zero] using (he (n + 1) hn x).symm
    obtain ⟨y, hy⟩ := ((ShortComplex.moduleCat_exact_iff _).mp hK') _ hx'
    change (koszulComplex A r f).X (r - n) at y
    change (koszulComplex A r f).d (r - n) (r - (n + 1)) y =
      e (n + 1) (by omega) x at hy
    refine ⟨(e n (by omega)).symm y, ?_⟩
    change (koszulDualComplex A r f).d n (n + 1) ((e n (by omega)).symm y) = x
    apply (e (n + 1) (by omega)).injective
    rw [he n (by omega), LinearEquiv.apply_symm_apply]
    exact hy

end ExteriorAlgebra
