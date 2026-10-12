module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Coprime.Basic

@[expose] public section

universe u

namespace Polynomial

/-! Auxiliary decomposition of the lifting theorem. -/

/-- The universal étale construction and the first coefficient reduction in Tag 0ALH;
the remaining coefficient reduction is isolated below for a separate proof.
Proof: follow the universal coprime factorization ring, the quotient section, and the
étale idempotent localization from the six-step proof of Tag 0ALH.
(blueprint: lem-weil-pbc-lift-monic-coprime-factorization-etale-core) -/
theorem exists_etale_lift_monic_coprime_factorization_core
    {A : Type u} [CommRing A] (I : Ideal A) (f : A[X]) (hf : f.Monic)
    (g₀ h₀ : (A ⧸ I)[X]) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀)
    (hcoprime : IsCoprime g₀ h₀) :
    ∃ (A' : Type u) (_ : CommRing A') (φ : A →+* A'),
      let J : Ideal A' := I.map φ
      let α : A ⧸ I →+* A' ⧸ J := Ideal.quotientMap J φ Ideal.le_comap_map
      AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) ∧
        Function.Bijective α ∧
        ∃ g' h' : A'[X], g'.Monic ∧ h'.Monic ∧ f.map φ = g' * h' ∧
          g'.map (Ideal.Quotient.mk J) = g₀.map α := by
  sorry

/-- The second factor reduction follows from the product identity and the first factor
reduction, coefficientwise in the quotient polynomial ring.
Proof: map the product identity to the quotient, rewrite the first factor by the
given reduction, and cancel the monic first factor using the prescribed factorization.
(blueprint: lem-weil-pbc-lift-monic-coprime-factorization-etale-h-reduction) -/
theorem lift_monic_coprime_factorization_h_reduction
    {A : Type u} [CommRing A] (I : Ideal A) (f : A[X])
    (g₀ h₀ : (A ⧸ I)[X]) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hfactor₀ : f.map (Ideal.Quotient.mk I) = g₀ * h₀)
    (A' : Type u) [CommRing A'] (φ : A →+* A')
    (g' h' : A'[X]) (hfactor : f.map φ = g' * h')
    (hgred : g'.map (Ideal.Quotient.mk (I.map φ)) =
      g₀.map (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    h'.map (Ideal.Quotient.mk (I.map φ)) =
      h₀.map (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map) := by
  sorry

end Polynomial
