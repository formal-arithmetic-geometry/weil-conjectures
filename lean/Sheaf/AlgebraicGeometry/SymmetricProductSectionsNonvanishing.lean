/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J8
-/
module

public import Sheaf.AlgebraicGeometry.SymmetricProductSections
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.NonvanishingTensorPullback
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardChartsNonvanishing
import Sheaf.AlgebraicGeometry.SymmetricProductSectionsPermutation
import WeilConjectures.AlgebraicGeometry.TensorSectionAffineOpen
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Nonvanishing of symmetric-product coefficient sections

The coefficient indexed by the vanishing second coordinates has exactly one nonzero
summand in the residue fibre. This proves generation without choosing fibre bases.
Source: symmetric-product-properties, proof steps 2–3; Stacks Tag 0A4F.
-/

@[expose] public section
universe v
open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem factorSection_cover {X S : Scheme.{v}} {n : ℕ}
    (pr : Fin n → (X ⟶ ℙ(ULift.{v} (Fin 2); S))) (i : Fin n) (z : X) :
    ∃ k : Fin 2, z ∈ nonvanishingLocus (symmetricProductFactor pr i)
      ((symmetricProductFactorSection pr i k).val (op ⊤)) := by
  have hcover := ProjectiveSpace.iSup_standardOpen (ULift.{v} (Fin 2)) S
  have hz : pr i z ∈ ⨆ k : ULift.{v} (Fin 2), ProjectiveSpace.standardOpen _ S k := by
    rw [hcover]
    trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  refine ⟨k.down, ?_⟩
  rw [factorSection_eval]
  apply (nonvanishing_tensorPullback (pr i) (ProjectiveSpace.twist _ S 1) _ z).mpr
  rw [ProjectiveSpace.projectiveSpace_standardCharts_part2]
  exact hk

private theorem nonvanishing_iff_residueValue_ne_zero {X : Scheme.{v}}
    (M : X.Modules) (s : Γ(M, ⊤)) (x : X) :
    x ∈ nonvanishingLocus M s ↔ residueValue s x trivial ≠ 0 := by
  have hz : residueValue s x trivial = 0 ↔
      M.presheaf.germ ⊤ x trivial s ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x) (M.presheaf.stalk x)) := by
    change (1 : IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗ₜ[X.presheaf.stalk x]
      M.presheaf.germ ⊤ x trivial s = 0 ↔ _
    rw [← (TensorProduct.quotTensorEquivQuotSMul
      ↑(M.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))).map_eq_zero_iff]
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]
  exact not_congr hz.symm

private theorem residueValue_sum {X : Scheme.{v}} (M : X.Modules) (z : X)
    {ι : Type*} (A : Finset ι) (t : ι → Γ(M, ⊤)) :
    residueValue (∑ i ∈ A, t i) z trivial = ∑ i ∈ A, residueValue (t i) z trivial := by
  simp only [residueValue, map_sum, TensorProduct.tmul_sum]

/-- The coefficient sections have no common zero for any family of morphisms to P¹.
Source: Stacks Tag 0A4F; symmetric-product-properties, proof steps 2 and 3.
(blueprint: lem-weil-pbc-symmetric-product-sections-nonvanishing)

Proof: At a point z, the coordinate pair in each factor is not both zero, since the
standard charts cover P¹ and nonvanishing is preserved by pullback. Let J be the subset
of factors where the second coordinate vanishes. In the tensor term indexed by J,
every chosen coordinate is nonzero, so that term is nonvanishing by the tensor-section
locus formula. Any other subset K with |K| = |J| omits an element of J and hence uses a
vanishing second coordinate there; that tensor term has zero residue value. Additivity
of residue values therefore identifies the value of F_|J| with the nonzero value of the
J term. The residue-value criterion gives the desired nonvanishing locus. -/
theorem symmetricProduct_sections_nonvanishing {S X : Scheme.{v}} (m : ℕ)
    (pr : Fin (m + 1) → (X ⟶ ℙ(ULift.{v} (Fin 2); S))) :
    ∀ z : X, ∃ j : ULift.{v} (Fin (m + 2)),
      z ∈ Scheme.Modules.nonvanishingLocus (symmetricProductLineBundle pr)
        ((symmetricProductCoordinateSection pr j).val (Opposite.op ⊤)) := by
  classical
  intro z
  have hfi : ∀ i, (symmetricProductFactor pr i).IsInvertible := fun i ↦
    ((invertible_pullback_tensor (pr i)).1 (ProjectiveSpace.twist _ S 1)).2
  let J : Finset (Fin (m + 1)) := Finset.univ.filter fun i ↦
    z ∉ nonvanishingLocus (symmetricProductFactor pr i)
      ((symmetricProductFactorSection pr i 1).val (op ⊤))
  let j : ULift.{v} (Fin (m + 2)) := ⟨⟨J.card, by
    have h := Finset.card_le_card (Finset.filter_subset
      (fun i ↦ z ∉ nonvanishingLocus (symmetricProductFactor pr i)
        ((symmetricProductFactorSection pr i 1).val (op ⊤))) Finset.univ)
    have h' : J.card ≤ m + 1 := by
      simpa only [J, Finset.card_univ, Fintype.card_fin] using h
    omega⟩⟩
  let t (K : Finset (Fin (m + 1))) := positiveTensorFamilySection m
    (symmetricProductFactor pr)
    (fun i ↦ symmetricProductFactorSection pr i (if i ∈ K then 0 else 1))
  have hloc (K : Finset (Fin (m + 1))) :
      z ∈ nonvanishingLocus (symmetricProductLineBundle pr) ((t K).val (op ⊤)) ↔
        ∀ i, z ∈ nonvanishingLocus (symmetricProductFactor pr i)
          ((symmetricProductFactorSection pr i (if i ∈ K then 0 else 1)).val (op ⊤)) := by
    change z ∈ nonvanishingLocus (positiveTensorFamily m (symmetricProductFactor pr))
      ((positiveTensorFamilySection m (symmetricProductFactor pr)
        (fun i ↦ symmetricProductFactorSection pr i (if i ∈ K then 0 else 1))).val
          (op ⊤)) ↔ _
    rw [(tensor_section_affine_open m (symmetricProductFactor pr) _).1]
    exact Set.mem_iInter
  have hgood : z ∈ nonvanishingLocus (symmetricProductLineBundle pr)
      ((t J).val (op ⊤)) := by
    apply (hloc J).mpr
    intro i
    by_cases hi : i ∈ J
    · rw [if_pos hi]
      have hy : z ∉ nonvanishingLocus (symmetricProductFactor pr i)
          ((symmetricProductFactorSection pr i 1).val (op ⊤)) :=
        (Finset.mem_filter.mp hi).2
      obtain ⟨k, hk⟩ := factorSection_cover pr i z
      fin_cases k
      · exact hk
      · exact (hy hk).elim
    · rw [if_neg hi]
      simpa only [J, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi
  have hbad (K : Finset (Fin (m + 1))) (hK : K.card = J.card) (hne : K ≠ J) :
      residueValue ((t K).val (op ⊤)) z trivial = 0 := by
    apply not_ne_iff.mp
    intro hv
    have hall := (hloc K).mp
      ((nonvanishing_iff_residueValue_ne_zero (symmetricProductLineBundle pr) _ z).mpr hv)
    have hsub : ¬ J ⊆ K := fun h ↦ hne
      (Finset.eq_of_subset_of_card_le h (by omega)).symm
    obtain ⟨i, hiJ, hiK⟩ := Finset.not_subset.mp hsub
    have hy := (Finset.mem_filter.mp hiJ).2
    apply hy
    simpa only [if_neg hiK] using hall i
  refine ⟨j, ?_⟩
  rw [nonvanishing_iff_residueValue_ne_zero]
  have hsum : (symmetricProductCoordinateSection pr j).val (op ⊤) =
      ∑ K ∈ (Finset.univ : Finset (Fin (m + 1))).powerset.filter
          (fun K ↦ K.card = J.card), (t K).val (op ⊤) :=
    unitHomEquiv_sum_eval _ _ _
  rw [hsum, residueValue_sum, Finset.sum_eq_single_of_mem J (by simp)]
  · exact (nonvanishing_iff_residueValue_ne_zero _ _ z).mp hgood
  · intro K hK hne
    exact hbad K (Finset.mem_filter.mp hK).2 hne

end AlgebraicGeometry
