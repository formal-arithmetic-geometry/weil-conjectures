module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! Uniqueness part of the henselian étale retraction theorem.

The standard étale presentation and simple-root uniqueness in Stacks Project, Tag 04GG,
show that two sections with the prescribed prime are equal.
(blueprint: lem-weil-pbc-henselian-etale-retraction-uniqueness)
-/

@[expose] public section

universe u

open AlgebraicGeometry

/-- The theorem is the uniqueness portion of Stacks Project Lemma Tag 04GG, implication
 (1) => (8).  Localize at an element outside q' and use a standard etale presentation.
 The two maps induce the same residue-field map, so their values on the presentation
 generator are roots congruent modulo the maximal ideal.  The standard-etale identity
 makes the derivative a unit; henselian simple-root uniqueness therefore identifies
 the generator images, and the universal property plus localization identifies the
 two algebra maps.  (blueprint: lem-weil-pbc-henselian-etale-retraction-uniqueness)
-/
theorem algHom_eq_of_henselianLocalRing_etale
    {S B : Type u} [CommRing S] [CommRing B] [HenselianLocalRing S]
    (φ : S →+* B)
    [AlgebraicGeometry.Etale (Scheme.Spec.map (CommRingCat.ofHom φ).op)]
    (q' : Ideal B) [q'.IsPrime]
    (hq : q'.comap φ = IsLocalRing.maximalIdeal S)
    (hres : Function.Bijective
      (Ideal.ResidueField.map (IsLocalRing.maximalIdeal S) q' φ hq.symm))
    [Algebra S B] (σ τ : B →ₐ[S] S)
    (hσ : (IsLocalRing.maximalIdeal S).comap σ.toRingHom = q')
    (hτ : (IsLocalRing.maximalIdeal S).comap τ.toRingHom = q') : σ = τ := by
  sorry
