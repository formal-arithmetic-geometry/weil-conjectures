/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import WeilConjectures.RingTheory.SyntomicPolynomialFibreComparison
import WeilConjectures.RingTheory.LocalizedIdealConormalGeneratorBound
import WeilConjectures.RingTheory.LciConormalFreeRankCodimension
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Fibre generators in a fixed polynomial presentation

Source: Stacks Project, Tag 00SY, proof of (3) implies (2); Tag 00SC.
(blueprint: lem-weil-pbc-syntomic-fibre-kernel-generators).
-/

set_option autoImplicit false

@[expose] public section

universe u v

namespace Algebra

private theorem lift_generators_from_localized_quotient
    {P A : Type*} [CommRing P] [CommRing A] [Algebra P A]
    (M : Submonoid P) [IsLocalization M A] (I : Ideal P) (m : Ideal A)
    (hfg : ((I.map (algebraMap P A)).map (Ideal.Quotient.mk m)).FG) :
    ∃ (c : ℕ) (f : Fin c → P),
      c = ((I.map (algebraMap P A)).map (Ideal.Quotient.mk m)).spanFinrank ∧
      Ideal.span (Set.range f) ≤ I ∧
      I.map (algebraMap P A) ≤
        (Ideal.span (Set.range f)).map (algebraMap P A) ⊔ m := by
  classical
  let π := Ideal.Quotient.mk m
  let K := (I.map (algebraMap P A)).map π
  obtain ⟨s, hsCard, hsSpan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  change Ideal.span (s : Set (A ⧸ m)) = K at hsSpan
  have hlift (x : s) : ∃ (a : I) (t : M),
      (x : A ⧸ m) * π (algebraMap P A t) = π (algebraMap P A a) := by
    have hx : (x : A ⧸ m) ∈ K := by
      rw [← hsSpan]
      exact Submodule.subset_span x.property
    obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective π
      Ideal.Quotient.mk_surjective).mp hx
    obtain ⟨⟨a, t⟩, hat⟩ := (IsLocalization.mem_map_algebraMap_iff M A).mp hy
    exact ⟨a, t, by rw [← hxy, ← map_mul, hat]⟩
  choose a t hat using hlift
  let f : Fin s.card → P := fun i ↦ a (s.equivFin.symm i)
  let J := (Ideal.span (Set.range f)).map (algebraMap P A)
  have hfI : Ideal.span (Set.range f) ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (a (s.equivFin.symm i)).property
  have hKJ : K ≤ J.map π := by
    rw [← hsSpan]
    apply Ideal.span_le.mpr
    intro x hx
    let z : s := ⟨x, hx⟩
    have hnum : π (algebraMap P A (a z)) ∈ J.map π := by
      apply Ideal.mem_map_of_mem
      apply Ideal.mem_map_of_mem
      apply Ideal.subset_span
      exact ⟨s.equivFin z, by simp [f]⟩
    have hu : IsUnit (π (algebraMap P A (t z))) :=
      (IsLocalization.map_units A (t z)).map π
    apply (Ideal.mul_unit_mem_iff_mem (J.map π) hu).mp
    exact (hat z).symm ▸ hnum
  refine ⟨s.card, f, hsCard, hfI, ?_⟩
  have hle := Ideal.map_le_iff_le_comap.mp hKJ
  simpa only [Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, π, Ideal.mk_ker, J] using hle

end Algebra
