/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.ClosedPointDimensionLocalRing
import WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Dimension lower bound for a polynomial quotient over a field

A nonzero quotient of `k[x₁, …, xₘ]` by `t` equations has dimension at least `m - t`.

## Implementation details

At a maximal ideal `M` containing the equations, `ht M = m` (Tag 00OP) and Krull's height theorem
(Tag 00KW) gives `m ≤ ht (M / J) + t`; the dimension of the spectrum bounds the local dimension
at the corresponding closed point.

## References

* [Stacks, Tag 00S9] (the paragraph following the definition)
* [Stacks, Tag 00OP]
* [Stacks, Tag 00KW]
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A nonzero quotient of an `m`-variable polynomial ring over a field by `t ≤ m`
equations has spectrum of Krull dimension at least `m - t`. -/
theorem sub_le_topologicalKrullDim_spec_mvPolynomial_quotient
    (k : Type u) [Field k] (m t : ℕ) (htm : t ≤ m)
    (f : Fin t → MvPolynomial (Fin m) k)
    [Nontrivial (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f))] :
    ((m - t : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim
      (Spec (CommRingCat.of (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))) := by
  classical
  let P := MvPolynomial (Fin m) k
  let J : Ideal P := Ideal.span (Set.range f)
  let T := P ⧸ J
  obtain ⟨n, hn⟩ := Ideal.exists_maximal (α := T)
  have : n.IsMaximal := hn
  let M : Ideal P := n.comap (Ideal.Quotient.mk J)
  have : M.IsMaximal := Ideal.comap_isMaximal_of_surjective
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hM : M.height = (m : ℕ∞) := by
    apply WithBot.coe_injective
    exact (IsLocalization.AtPrime.ringKrullDim_eq_height M
      (Localization.AtPrime M)).symm.trans
      (MvPolynomial.ringKrullDim_localizationAtMaximal m M)
  have hsubset : Set.range f ⊆ M := by
    rintro _ ⟨i, rfl⟩
    change Ideal.Quotient.mk J (f i) ∈ n
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))]
    exact n.zero_mem
  have hheight := Ideal.height_le_height_add_encard_of_subset (Set.range f) hsubset
  have hmap : M.map (Ideal.Quotient.mk J) = n :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  have hcard : (Set.range f).encard ≤ (t : ℕ∞) := by
    simpa only [Set.image_univ, Set.encard_univ, ENat.card_eq_coe_fintype_card,
      Fintype.card_fin] using Set.encard_image_le f Set.univ
  rw [hM, hmap] at hheight
  have hbound : (m : ℕ∞) ≤ n.height + t :=
    hheight.trans (add_le_add_right hcard _)
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp (n.height_ne_top hn.ne_top)
  rw [← hd] at hbound
  have hnat : m ≤ d + t := by exact_mod_cast hbound
  have hlocal : ((m - t : ℕ) : WithBot ℕ∞) ≤
      topologicalKrullDimAt (⟨n, inferInstance⟩ : Spec (CommRingCat.of T)) := by
    rw [topologicalKrullDimAt_eq_ringKrullDim_localizationAtMaximal
      ⟨m, Ideal.Quotient.mkₐ k J, Ideal.Quotient.mk_surjective⟩ n,
      IsLocalization.AtPrime.ringKrullDim_eq_height n (Localization.AtPrime n), ← hd]
    apply WithBot.coe_le_coe.mpr
    exact_mod_cast (show m - t ≤ d by omega)
  rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt]
  exact hlocal.trans (le_iSup (fun x : Spec (CommRingCat.of T) ↦
    topologicalKrullDimAt x) ⟨n, inferInstance⟩)

end AlgebraicGeometry
