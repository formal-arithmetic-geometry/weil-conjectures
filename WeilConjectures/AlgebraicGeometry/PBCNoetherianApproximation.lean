/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.MvPolynomial.Basic
import WeilConjectures.RingTheory.PolynomialQuotientDimensionLowerBound
import Mathlib.RingTheory.Extension.Presentation.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import WeilConjectures.AlgebraicGeometry.NoetherianCoefficientNeighborhood
import WeilConjectures.AlgebraicGeometry.NoetherianBoundedCoverDescent

/-! # Noetherian approximation of a relative global complete intersection

## References

* Stacks Project, Algebra, Tag 00SU.
-/

@[expose] public section

universe u

namespace Algebra

/-- The coefficient ring is constructed by adjoining the finite union of coefficient sets. -/
private theorem finite_coefficient_model
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R) :
    ∃ (R₀ : Subring R), Algebra.FiniteType ℤ R₀ ∧
      ∃ f₀ : Fin c → MvPolynomial (Fin n) R₀,
        ∀ i, MvPolynomial.map R₀.subtype (f₀ i) = f i := by
  classical
  let t : Set R := ⋃ i, ((f i).coeffs : Set R)
  have ht : t.Finite := Set.finite_iUnion fun i ↦ (f i).coeffs.finite_toSet
  let A := Algebra.adjoin ℤ t
  have hA : Algebra.FiniteType ℤ A := Algebra.FiniteType.adjoin_of_finite ht
  have hcoeff (i : Fin c) :
      ((f i).coeffs : Set R) ⊆ Set.range A.toSubring.subtype := by
    intro r hr
    exact ⟨⟨r, Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, hr⟩)⟩, rfl⟩
  choose f₀ hf₀ using fun i ↦ MvPolynomial.mem_range_map_iff_coeffs_subset.mpr (hcoeff i)
  exact ⟨A.toSubring, hA, f₀, hf₀⟩

/-- A nonempty original spectrum forces the equation count to be at most the variable count. -/
private theorem equation_count_le_of_point
    {R : Type u} [CommRing R] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation f)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) : c ≤ n := by
  let S := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
  let p := PrimeSpectrum.comap (algebraMap R S) q
  have hn : Nontrivial (p.asIdeal.Fiber S) :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap p).mpr ⟨q, rfl⟩
  exact (h p.asIdeal hn).1

/-- Scalar extension identifies a fibre with the quotient by the residue-field equations. -/
private theorem polynomial_quotient_fibre_lower_bound
    {R : Type u} [CommRing R] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    (hc : c ≤ n) (p : Ideal R) [p.IsPrime]
    (hn : Nontrivial (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) :
    ((n - c : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim
      (PrimeSpectrum (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) := by
  classical
  let k := p.ResidueField
  let P := (Presentation.naive (v := f)).baseChange k
  let e := (Ideal.quotientEquivAlgOfEq k P.span_range_relation_eq_ker).trans
    (P.quotientEquiv.restrictScalars k)
  have : Nontrivial (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) := hn
  have : Nontrivial (MvPolynomial (Fin n) k ⧸ Ideal.span
      (Set.range (fun i ↦ MvPolynomial.map (algebraMap R k) (f i)))) :=
    e.toEquiv.nontrivial
  have hl := AlgebraicGeometry.sub_le_topologicalKrullDim_spec_mvPolynomial_quotient
    k n c hc (fun i ↦ MvPolynomial.map (algebraMap R k) (f i))
  have hd := IsHomeomorph.topologicalKrullDim_eq
    (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv)
    (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).isHomeomorph
  change ((n - c : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim
    (PrimeSpectrum (MvPolynomial (Fin n) k ⧸ Ideal.span
      (Set.range (fun i ↦ MvPolynomial.map (algebraMap R k) (f i))))) at hl
  exact hl.trans_eq hd

/-- Descend the specified complete-intersection presentation to a finite type subring
(Stacks, Tag 00SU). -/
theorem exists_finiteType_subring_relativeGlobalCompleteIntersection
    (R : Type u) [CommRing R] (n c : ℕ)
    (f : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation f) :
    ∃ (R₀ : Subring R), Algebra.FiniteType ℤ R₀ ∧
      ∃ (f₀ : Fin c → MvPolynomial (Fin n) R₀),
        (∀ (i : Fin c) (d : Fin n →₀ ℕ),
          (AddMonoidAlgebra.coeff (f i) d) = (((AddMonoidAlgebra.coeff (f₀ i) d) : R₀) : R)) ∧
        IsRelativeGlobalCompleteIntersectionPresentation f₀ := by
  classical
  obtain ⟨R₀, hR₀, f₀, hf₀⟩ := finite_coefficient_model R n c f
  let S := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
  choose G hG hbound using
    exists_coefficient_model_principal_neighborhood R n c f h R₀ f₀ hf₀
  obtain ⟨R₁, hR₁, f₁, hf₁, hupper⟩ :=
    exists_finiteType_model_of_bounded_principal_cover R n c (n - c) f R₀ hR₀ f₀ hf₀
      (PrimeSpectrum S) G (fun q ↦ ⟨q, hG q⟩) hbound
  refine ⟨R₁, hR₁, f₁, ?_, ?_⟩
  · intro i d
    have hc := congrArg (fun f ↦ AddMonoidAlgebra.coeff f d) (hf₁ i)
    exact hc.symm.trans (MvPolynomial.coeff_map R₁.subtype (f₁ i) d)
  · intro p hp hn
    obtain ⟨⟨q⟩, hu⟩ := hupper p hn
    have hc : c ≤ n := equation_count_le_of_point f h q
    exact ⟨hc, le_antisymm hu (polynomial_quotient_fibre_lower_bound f₁ hc p hn)⟩

end Algebra
