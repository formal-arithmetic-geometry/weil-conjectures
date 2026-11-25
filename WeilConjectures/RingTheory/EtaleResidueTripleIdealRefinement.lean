/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples

import Mathlib.RingTheory.Unramified.LocalRing
import WeilConjectures.RingTheory.EtaleResidueTripleUnitRefinement

/-!
# Ideal refinement of étale residue triples

Every element of the prime of a pointed étale residue triple over `(R, p)` maps into `p` times
the ring of some later triple.

## Implementation details

Since the map is étale, `p B_q = q B_q`, so for `f ∈ q` there is `g ∉ q` with `g f ∈ p B`;
the principal localization `B_g` gives the required triple and morphism.

## References

* Stacks Project, Algebra, Tags 04GN, 04GP, 00U4
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- For an element `f` of the prime `q` of an étale residue triple `t`, there is a morphism of
triples `t ⟶ s` sending `f` into the extension of `p` to the ring of `s`. -/
theorem etaleResidueTriple_ideal_refinement
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (t : EtaleResidueTriples R p K χ) (f : t.B) (hf : f ∈ t.q.asIdeal) :
    ∃ (s : EtaleResidueTriples R p K χ) (a : t ⟶ s),
      ((etaleResidueTriplesRingDiagram R p K χ).map a).hom f ∈
        p.asIdeal.map s.α.hom := by
  let : Algebra R t.B := t.α.hom.toAlgebra
  have he : t.α.hom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp t.etale
  let : Algebra.Etale R t.B := (RingHom.etale_algebraMap).mp he
  let : t.q.asIdeal.LiesOver p.asIdeal := ⟨by
    have h := congrArg PrimeSpectrum.asIdeal t.over
    exact h.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p.asIdeal t.q.asIdeal
  have hid := (Algebra.isUnramifiedAt_iff_map_eq R p.asIdeal t.q.asIdeal).mp
    (inferInstance : Algebra.IsUnramifiedAt R t.q.asIdeal)
  have hmem : algebraMap t.B (Localization.AtPrime t.q.asIdeal) f ∈
      (p.asIdeal.map t.α.hom).map
        (algebraMap t.B (Localization.AtPrime t.q.asIdeal)) := by
    rw [Ideal.map_map]
    change algebraMap t.B (Localization.AtPrime t.q.asIdeal) f ∈
      p.asIdeal.map (algebraMap R (Localization.AtPrime t.q.asIdeal))
    rw [hid.2, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hf
  obtain ⟨g, hg, hgf⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff t.q.asIdeal.primeCompl
      (Localization.AtPrime t.q.asIdeal) (p.asIdeal.map t.α.hom) f).mp hmem
  obtain ⟨s, a, ha⟩ := etaleResidueTriple_unit_refinement R p K χ t g hg
  refine ⟨s, a, ?_⟩
  let β := (etaleResidueTriplesRingDiagram R p K χ).map a
  have hw : t.α ≫ β = s.α := by
    exact congrArg Over.Hom.left (Under.w a.hom)
  have hm : β.hom (g * f) ∈ p.asIdeal.map s.α.hom := by
    rw [← hw, CommRingCat.hom_comp, ← Ideal.map_map]
    exact Ideal.mem_map_of_mem β.hom hgf
  rw [map_mul] at hm
  exact (Ideal.unit_mul_mem_iff_mem _ ha).mp hm

end AlgebraicGeometry.Scheme
