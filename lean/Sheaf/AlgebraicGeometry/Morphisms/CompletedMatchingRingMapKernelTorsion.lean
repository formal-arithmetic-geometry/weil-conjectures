/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

import Mathlib.RingTheory.Finiteness.Ideal
public import Sheaf.AlgebraicGeometry.Morphisms.CompletedMatchingRingMap
import Sheaf.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapKernelLocalTorsion

/-! # CompletedMatchingRingMapKernelTorsion

Source: Stacks Project, Tags 0BLH, 05ER and 05EU.
(blueprint: lem-sbc-completed-matching-ring-map-kernel-torsion)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

private theorem ideal_pow_mul_annihilates
    {R P : Type u} [CommRing R] [CommRing P] (φ : R →+* P)
    {I : Ideal R} (hI : I.FG) {t : ℕ} (f : Fin t → R)
    (hf : I = Ideal.span (Set.range f)) (x : P)
    (hx : ∀ i, ∃ e : ℕ, (φ (f i)) ^ e * x = 0) :
    ∃ n : ℕ, ∀ a ∈ I ^ n, φ a * x = 0 := by
  let : Algebra R P := φ.toAlgebra
  have haux : ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0 := by
    let J : Ideal R := (Submodule.span R ({x} : Set P)).annihilator
    have hIJ : I ≤ J.radical := by
      rw [hf]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      obtain ⟨e, he⟩ := hx i
      apply (Ideal.mem_radical_iff).2
      refine ⟨e, ?_⟩
      have he' : f i ^ e • x = 0 := by
        rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_pow]
        exact he
      exact (Submodule.mem_annihilator_span_singleton x _).2 he'
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ hI
    refine ⟨n, ?_⟩
    intro a ha
    exact (Submodule.mem_annihilator_span_singleton x a).1 (hn ha)
  obtain ⟨n, hn⟩ := haux
  refine ⟨n, ?_⟩
  intro a ha
  simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hn a ha

/-- Kernel elements are maximal-ideal-power torsion.
Source: Stacks Project, Tag 05ER, localized comparison argument, applied as in 0BLH.
Proof: put m = maximalIdeal A, C = its completion, and B = D.matchingRing.
Choose finitely many generators f_i of m. The opens D(f_i) cover U by hU.
The inverse images of these opens in Y are affine, since q is finite; write
B_i for their section rings and B' for the section ring of the affine scheme E.
The overlap isomorphism gives B'_f_i = C tensor_A B_i, compatibly on double
intersections. Sheaf gluing on this finite cover identifies B with the module
of compatible families H0 for these formal-gluing data. The ring-pushout
universal property identifies the source with C tensor_A B, and the comparison
with c tensor b maps to c times the completed coordinate of b.
Completion is flat. The H0 localization theorem (05EP and 05EQ, as used in
05ER) identifies B_f_i with B_i, respecting the coordinate projections.
Consequently the localization of the comparison at each f_i is an isomorphism.
A kernel element x therefore satisfies f_i^e_i * x = 0 for some e_i for each i.
Take N = 1 + sum_i e_i. Every degree-N monomial in the generators contains
some f_i^e_i, so every element of m^N kills x. Multiplication by a in A here
is precisely multiplication by (D.baseMap followed by pushout.inl)(a).
For an empty generator family m = 0 and m^1 kills every element. If U is
empty with a nonempty family, all the localized chart rings are zero, so the
same localization and monomial argument applies. Zero component rings cause
no exception.
(blueprint: lem-sbc-completed-matching-ring-map-kernel-torsion) -/
theorem completedRingMap_kernel_torsion
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    ∀ x, D.completedRingMap x = 0 → ∃ n : ℕ,
      ∀ a ∈ IsLocalRing.maximalIdeal A ^ n,
        (D.baseMap ≫ pushout.inl _ _).hom a * x = 0 := by
  intro x hx
  have hfg : (IsLocalRing.maximalIdeal A).FG :=
    Ideal.fg_of_isNoetherianRing _
  obtain ⟨t, f, hf, hlocal⟩ := D.completedRingMap_kernel_local_torsion hU x hx
  exact ideal_pow_mul_annihilates (D.baseMap ≫ pushout.inl _ _).hom hfg f hf x hlocal

end AlgebraicGeometry.Scheme.CompletionGluingData
