module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Sheaf.RingTheory.HenselianLocalRootLifting

/-! Existence part of the henselian étale retraction theorem.

This is the existence portion of the six-step argument in Stacks Project, Tag 04GG,
using the standard étale presentation and simple-root lifting.
(blueprint: lem-weil-pbc-henselian-etale-retraction-existence)
-/

@[expose] public section

universe u

open AlgebraicGeometry

/-- The theorem is the existence portion of Stacks Project Lemma Tag 04GG, implication
 (1) => (8).  Reduce the etale algebra locally to a standard etale presentation,
 identify the given residue-field point with a simple root of the defining polynomial,
 lift that root by the root-lifting characterization of a henselian local ring, and
 use the standard-etale universal property to obtain the algebra map.  Localization
 at an element outside q' descends this map to B and the residue calculation gives
 the stated inverse image of the maximal ideal.
 (blueprint: lem-weil-pbc-henselian-etale-retraction-existence)
-/
theorem exists_algHom_of_henselianLocalRing_etale
    {S B : Type u} [CommRing S] [CommRing B] [HenselianLocalRing S]
    (φ : S →+* B)
    [AlgebraicGeometry.Etale (Scheme.Spec.map (CommRingCat.ofHom φ).op)]
    (q' : Ideal B) [q'.IsPrime]
    (hq : q'.comap φ = IsLocalRing.maximalIdeal S)
    (hres : Function.Bijective
      (Ideal.ResidueField.map (IsLocalRing.maximalIdeal S) q' φ hq.symm)) :
    letI : Algebra S B := φ.toAlgebra
    ∃ σ : B →ₐ[S] S,
      (IsLocalRing.maximalIdeal S).comap σ.toRingHom = q' := by
  sorry
