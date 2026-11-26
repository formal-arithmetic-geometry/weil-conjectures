/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import WeilConjectures.RingTheory.HenselianEtaleRetractionExistence
import WeilConjectures.RingTheory.HenselianEtaleRetractionUniqueness

/-!
# Retractions of étale algebras over henselian local rings

Let `S` be a henselian local ring and `B` an étale `S`-algebra. Every prime `q'` of `B` over the
maximal ideal of `S` with trivial residue field extension is the preimage of the maximal ideal
under exactly one `S`-algebra retraction `B →ₐ[S] S`
(`existsUnique_algHom_of_henselianLocalRing_etale`). Existence and uniqueness are proved in
separate files.

## References

* [Stacks, Tag 04GG]
-/

@[expose] public section

universe u

open AlgebraicGeometry

/-- A residue-rational point of an étale algebra over a henselian local ring
has a unique section back to the base ring.
-/
theorem existsUnique_algHom_of_henselianLocalRing_etale
    {S B : Type u} [CommRing S] [CommRing B] [HenselianLocalRing S]
    (φ : S →+* B)
    [AlgebraicGeometry.Etale (Scheme.Spec.map (CommRingCat.ofHom φ).op)]
    (q' : Ideal B) [q'.IsPrime]
    (hq : q'.comap φ = IsLocalRing.maximalIdeal S)
    (hres : Function.Bijective
      (Ideal.ResidueField.map (IsLocalRing.maximalIdeal S) q' φ hq.symm)) :
    letI : Algebra S B := φ.toAlgebra
    ∃! σ : B →ₐ[S] S,
      (IsLocalRing.maximalIdeal S).comap σ.toRingHom = q' := by
  set_option linter.style.haveILetI false in
    letI : Algebra S B := φ.toAlgebra
  obtain ⟨σ, hσ⟩ := exists_algHom_of_henselianLocalRing_etale φ q' hq hres
  refine ⟨σ, hσ, ?_⟩
  intro τ hτ
  exact (algHom_eq_of_henselianLocalRing_etale φ q' hq hres σ τ hσ hτ).symm
