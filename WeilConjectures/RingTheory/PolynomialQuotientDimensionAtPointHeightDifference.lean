/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Ideal.Height
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.DimensionAtPointComponents
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg
import WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension

/-!
# Dimension at a point of a polynomial quotient

The dimension at a point `q` of `Spec(k[x₁, …, xₙ] / I)` is `n - h' + h`, where `h` is the height
of `q` and `h'` the height of its inverse image in the polynomial ring.

## Implementation details

The dimension at a point of a finite type algebra is the height plus the transcendence degree of
the residue field (Tag 00P1); the two residue fields agree, so the difference of the dimensions
is `h' - h` (Tag 00P2), and the polynomial ring has dimension `n` at every point (Tag 00OP).

## References

* [Stacks, Tag 00P2]
* [Stacks, Tag 00P1]
* [Stacks, Tag 00OP]
* [Stacks, Tag 00SC]
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- For a prime `q` of `k[x₁, …, xₙ] / I`, the heights `h` of `q` and `h'` of its inverse image
in the polynomial ring are finite with `h ≤ h' ≤ n`, and the dimension of `Spec` of the quotient
at `q` is `n - h' + h`. -/
theorem topologicalKrullDimAt_polynomial_quotient_eq_height_difference
    {k : Type u} [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k))
    (q : Ideal (MvPolynomial (Fin n) k ⧸ I)) [q.IsPrime] :
    ∃ h h' : ℕ,
      q.height = (h : ℕ∞) ∧
      (q.comap (Ideal.Quotient.mk I)).height = (h' : ℕ∞) ∧
      h ≤ h' ∧ h' ≤ n ∧
      topologicalKrullDimAt
        (⟨q, inferInstance⟩ : Spec (CommRingCat.of (MvPolynomial (Fin n) k ⧸ I))) =
        ((n - h' + h : ℕ) : WithBot ℕ∞) := by
  classical
  let p := q.comap (Ideal.Quotient.mk I)
  obtain ⟨d, r, hd, hr, hdim⟩ :=
    topologicalKrullDimAt_eq_ringKrullDim_add_trdeg (k := k) q
  obtain ⟨d', r', hd', hr', hdim'⟩ :=
    topologicalKrullDimAt_eq_ringKrullDim_add_trdeg (k := k) p
  have hq : q.height = (d : ℕ∞) := by
    exact_mod_cast (IsLocalization.AtPrime.ringKrullDim_eq_height q _).symm.trans hd
  have hp : p.height = (d' : ℕ∞) := by
    exact_mod_cast (IsLocalization.AtPrime.ringKrullDim_eq_height p _).symm.trans hd'
  let f : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k ⧸ I :=
    Ideal.Quotient.mkₐ k I
  let e : p.ResidueField ≃ₐ[k] q.ResidueField :=
    AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ p q f rfl)
      (RingHom.SurjectiveOnStalks.residueFieldMap_bijective
        (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
        p q rfl)
  have hrr : r' = r := by
    have he := e.trdeg_eq
    rw [hr', hr] at he
    exact_mod_cast he
  obtain ⟨qs, hqs, hne, a, ha, hupper, hcomp, hquot, hquot', hmax, m, hm, hpm, hma⟩ :=
    dimension_at_point_components (k := k) p
  have : m.IsMaximal := hm
  have han : (a : WithBot ℕ∞) = (n : WithBot ℕ∞) :=
    hma.symm.trans (MvPolynomial.ringKrullDim_localizationAtMaximal n m)
  have hsum : d' + r = n := by
    have he := hdim'.symm.trans (ha.trans han)
    rw [hrr] at he
    exact_mod_cast he
  have hheight : q.height ≤ p.height := by
    change (⟨q, inferInstance⟩ : PrimeSpectrum _).asIdeal.height ≤
      (PrimeSpectrum.comap (Ideal.Quotient.mk I) ⟨q, inferInstance⟩).asIdeal.height
    rw [PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.height_eq_orderHeight]
    apply Order.height_le_height_apply_of_strictMono
    intro x y hxy
    change x.asIdeal.comap (Ideal.Quotient.mk I) < y.asIdeal.comap (Ideal.Quotient.mk I)
    exact (Ideal.orderEmbeddingOfSurjective
      (f := Ideal.Quotient.mk I) (Ideal.Quotient.mk_surjective (I := I))).strictMono hxy
  have hdd : d ≤ d' := by
    rw [hq, hp] at hheight
    exact_mod_cast hheight
  refine ⟨d, d', hq, hp, hdd, ?_, ?_⟩
  · omega
  · have hle : d' ≤ n := by omega
    have harith : d + r = n - d' + d := by omega
    simpa [harith] using hdim

end AlgebraicGeometry
