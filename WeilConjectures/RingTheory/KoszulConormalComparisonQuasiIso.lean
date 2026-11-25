/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulConormalComparison
public import WeilConjectures.RingTheory.KoszulRegularSequence
import WeilConjectures.RingTheory.KoszulConormalBasis
import WeilConjectures.RingTheory.KoszulDualBelowTopHomology
import WeilConjectures.RingTheory.KoszulConormalTopHomology
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Quasi-isomorphism of a normalized dual Koszul comparison

Every determinant-normalized comparison from the dual Koszul complex of a Koszul-regular
sequence to the normal determinant is a quasi-isomorphism.

## Implementation details

The signed complementary-wedge equivalences identify the dual Koszul complex with the Koszul
complex, so it is exact outside degree `r`, where its cohomology is `A/I`. The conormal basis
makes the normal determinant free of rank one, and the normalization (applied to the standard
basis) forces the top component to be the quotient map times a unit.

## References

* [Stacks, Tags 0BQZ, 062I]
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

private theorem koszulDual_isZero_homology_above_top
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (n : ℕ) (hn : r < n) :
    CategoryTheory.Limits.IsZero ((koszulDualComplex A r f).homology n) := by
  classical
  let b := (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower n
  have : IsEmpty (Set.powersetCard (Fin r) n) := ⟨fun s ↦ by
    have hcard : s.val.card ≤ r := by simpa using Finset.card_le_univ s.val
    exact (Nat.not_le_of_lt hn) (s.property ▸ hcard)⟩
  have : Subsingleton (⋀[A]^n (Fin r →₀ A)) := b.repr.injective.subsingleton
  have : Subsingleton ((koszulComplex A r f).X n ⟶ ModuleCat.of A A) := by
    change Subsingleton (ModuleCat.of A (⋀[A]^n (Fin r →₀ A)) ⟶ ModuleCat.of A A)
    refine ⟨fun x y ↦ ?_⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  have hX : CategoryTheory.Limits.IsZero ((koszulDualComplex A r f).X n) := by
    change CategoryTheory.Limits.IsZero
      (ModuleCat.of A ((koszulComplex A r f).X n ⟶ ModuleCat.of A A))
    exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  exact (HomologicalComplex.ExactAt.of_isZero hX).isZero_homology

/-- Every determinant-normalized comparison is a quasi-isomorphism. -/
theorem koszul_conormal_comparison_is_quasiIso
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I)
    (φ : koszulDualComplex A r f ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
        (koszulNormalDeterminant A I r))
    (hφ : IsKoszulConormalComparison A I r f hf φ) : QuasiIso φ := by
  obtain ⟨b, hb⟩ := exists_koszul_conormal_basis A I r f hreg hf
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hn : n = r
  · subst n
    exact koszul_conormal_comparison_isIso_top_homology A I r f hf b hb φ hφ
  · have hsource : CategoryTheory.Limits.IsZero ((koszulDualComplex A r f).homology n) := by
      rcases Nat.lt_or_gt_of_ne hn with hlt | hgt
      · exact koszulDual_isZero_homology_below_top A r f hreg n hlt
      · exact koszulDual_isZero_homology_above_top A r f n hgt
    have htarget := HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.up ℕ) r (koszulNormalDeterminant A I r) n hn
    exact hsource.isIso htarget (HomologicalComplex.homologyMap φ n)

end ExteriorAlgebra
