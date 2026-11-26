/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.DimensionAtPointComponents
import WeilConjectures.RingTheory.MinimalComponentDimensionMaximum
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.FieldTheory.FinTrdeg

/-!
# Dimension at a point of a finite type algebra over a field

## Implementation details

Natural-number witnesses express finiteness without losing the cardinal-valued meaning of
`Algebra.trdeg`. With `r = trdeg_k κ(p)`, maximal chains above `p` have length `r`; for the
finitely many minimal primes `q_j ⊆ p` with maximal chains to `p` of length `s(j)`, one has
`dim S_p = max_j s(j)` and `dim (S/q_j) = s(j) + r`, so the components description of the
dimension at a point gives `dim_p Spec S = dim S_p + r`.

## References

* [Stacks, Tag 00P1]
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- The local topological dimension, local-ring dimension, and residue-field transcendence degree
are finite, and the first is the sum of the other two. -/
theorem topologicalKrullDimAt_eq_ringKrullDim_add_trdeg
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsPrime] :
    ∃ d r : ℕ,
      ringKrullDim (Localization.AtPrime p) = (d : WithBot ℕ∞) ∧
      Algebra.trdeg k p.ResidueField = (r : Cardinal.{v}) ∧
      topologicalKrullDimAt (⟨p, inferInstance⟩ : Spec (CommRingCat.of S)) =
        ((d + r : ℕ) : WithBot ℕ∞) := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp
    (ringKrullDim_ne_bot (R := Localization.AtPrime p))
  have hat : a ≠ ⊤ := by
    intro h
    apply ringKrullDim_ne_top (R := Localization.AtPrime p)
    rw [← ha, h]
    rfl
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hat
  have hdim : ringKrullDim (Localization.AtPrime p) = (d : WithBot ℕ∞) :=
    ha.symm.trans (congrArg (fun a : ℕ∞ ↦ (a : WithBot ℕ∞)) hd.symm)
  have : Algebra.EssFiniteType k p.ResidueField := .comp k S p.ResidueField
  obtain ⟨r, htrdeg⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0 k p.ResidueField)
  obtain ⟨hbound, q, hq, hqp, hminimal, hqeq⟩ :=
    minimal_component_dimension_maximum (k := k) p d r hdim htrdeg
  obtain ⟨qs, hqs, _, n, hn, _, _, hquot, hquot', _⟩ :=
    dimension_at_point_components (k := k) p
  obtain ⟨q', hq', hq'eq⟩ := hquot'
  have hle : (n : WithBot ℕ∞) ≤ ((d + r : ℕ) : WithBot ℕ∞) := by
    obtain ⟨hprime, hbelow, hmin⟩ := (hqs q').mp hq'
    rw [← hq'eq]
    exact hbound q' hprime hbelow hmin
  have hge : ((d + r : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
    rw [← hqeq]
    exact hquot q ((hqs q).mpr ⟨hq, hqp, hminimal⟩)
  exact ⟨d, r, hdim, htrdeg, hn.trans (le_antisymm hle hge)⟩

end AlgebraicGeometry
