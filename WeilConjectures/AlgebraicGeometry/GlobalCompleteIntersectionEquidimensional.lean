/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.PolynomialQuotientDimensionAtPointHeightDifference
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# A global complete intersection has the expected dimension at every point

## References

* Stacks Project, Tag 00S8 and the following paragraph.
-/

@[expose] public section


universe u

namespace AlgebraicGeometry

/-- A nonzero quotient of a polynomial ring in `m` variables over a field by `t ≤ m` equations
has local dimension at least `m - t` at every prime (Stacks, Tag 00S8). -/
/- Lower bound on local dimensions. -/
theorem topologicalKrullDimAt_spec_quotient_mvPolynomial_lower_bound
    (k : Type u) [Field k] (m t : ℕ)
    (f : Fin t → MvPolynomial (Fin m) k)
    (hT : Nontrivial (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))
    (htm : t ≤ m) :
    ∀ p : PrimeSpectrum (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)),
      ((m - t : ℕ) : WithBot ℕ∞) ≤
        topologicalKrullDimAt
          (⟨p, inferInstance⟩ :
            Spec (CommRingCat.of (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))) := by
  intro p
  classical
  let _ := hT
  let P := MvPolynomial (Fin m) k
  let J : Ideal P := Ideal.span (Set.range f)
  let T := P ⧸ J
  let q : Ideal P := p.asIdeal.comap (Ideal.Quotient.mk J)
  obtain ⟨d, d', hd, hd', hdd, hdm, hdim⟩ :=
    topologicalKrullDimAt_polynomial_quotient_eq_height_difference m J p.asIdeal
  have hsubset : Set.range f ⊆ q := by
    rintro _ ⟨i, rfl⟩
    change Ideal.Quotient.mk J (f i) ∈ p.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self i))]
    exact p.asIdeal.zero_mem
  have hheight := Ideal.height_le_height_add_encard_of_subset (Set.range f) hsubset
  have hmap : q.map (Ideal.Quotient.mk J) = p.asIdeal :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  have hcard : (Set.range f).encard ≤ (t : ℕ∞) := by
    simpa only [Set.image_univ, Set.encard_univ, ENat.card_eq_coe_fintype_card,
      Fintype.card_fin] using Set.encard_image_le f Set.univ
  rw [hmap, hd, hd'] at hheight
  have hbound : (d' : ℕ∞) ≤ (d : ℕ∞) + t :=
    hheight.trans (add_le_add_right hcard _)
  have hnat : d' ≤ d + t := by exact_mod_cast hbound
  rw [hdim]
  apply WithBot.coe_le_coe.mpr
  have harith : m - t ≤ m - d' + d := by omega
  exact_mod_cast harith

/-- A nonzero quotient of a polynomial ring in `m` variables over a field by `t` equations whose
spectrum has dimension `m - t` (with `t ≤ m`) has local dimension `m - t` at every prime. -/
theorem topologicalKrullDimAt_spec_quotient_mvPolynomial_of_eq
    (k : Type u) [Field k] (m t : ℕ)
    (f : Fin t → MvPolynomial (Fin m) k)
    (hT : Nontrivial (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))
    (hDim : t ≤ m ∧
      topologicalKrullDim
          (Spec (CommRingCat.of (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))) =
        ((m - t : ℕ) : WithBot ℕ∞)) :
    ∀ p : PrimeSpectrum (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)),
      topologicalKrullDimAt
          (⟨p, inferInstance⟩ :
            Spec (CommRingCat.of (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))) =
        ((m - t : ℕ) : WithBot ℕ∞) := by
  intro p
  let X := Spec (CommRingCat.of (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))
  let x : X := ⟨p, inferInstance⟩
  apply le_antisymm
  · have hupper : topologicalKrullDimAt x ≤ topologicalKrullDim X := by
      unfold topologicalKrullDimAt
      have h : (⨅ U : TopologicalSpace.Opens X, ⨅ (_ : x ∈ U), topologicalKrullDim U) ≤
        topologicalKrullDim (⊤ : TopologicalSpace.Opens X) :=
      iInf₂_le (α := WithBot ℕ∞) ⊤ trivial
      have he := IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ X)
        (Homeomorph.Set.univ X).isHomeomorph
      rw [← he]
      exact h
    change topologicalKrullDimAt x ≤ _
    exact hupper.trans_eq hDim.2
  · exact topologicalKrullDimAt_spec_quotient_mvPolynomial_lower_bound
      k m t f hT hDim.1 p

end AlgebraicGeometry
