/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.PBCNoetherianApproximation
import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionBaseChange
import WeilConjectures.RingTheory.RelativeCompleteIntersectionNoetherianRegularSequence
import WeilConjectures.RingTheory.PolynomialLocalWeakRegularSequenceDescent

/-!
# Local regularity of equations of a relative global complete intersection

The equations of a relative global complete intersection form a regular sequence in the
polynomial local ring at the inverse image of any prime of the quotient.

## Implementation details

For Noetherian `R`, the equations are regular in the closed fibre of the flat local map
`R_p → R[x]_Q` (base change, Tag 00SS, and the field case, Tag 00SC), and Tag 00MG lifts this.
For arbitrary `R`, the presentation descends to a finite type `ℤ`-subalgebra (Tag 00SU); the
polynomial local ring and its partial quotients are filtered colimits over the finitely
generated subrings containing it, and exactness of filtered colimits (Tag 00DB) preserves the
injectivity of multiplication by each equation. The final quotient is a localization of the
given quotient at a prime, hence nonzero.

## References

* [Stacks, Tag 00SV] (1)
* [Stacks, Tags 00SS, 00SC, 00MG, 00SU, 00DB]
-/

@[expose] public section

universe w

namespace Algebra

/-- The equations of a relative global complete intersection presentation form a regular
sequence in the polynomial local ring at the inverse image of any prime of its quotient. -/
theorem isRegular_localization_of_relativeGlobalCompleteIntersection
    {R : Type w} [CommRing R] {n c : ℕ}
    (relations : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation relations)
    (q : Ideal (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range relations))) [q.IsPrime] :
    RingTheory.Sequence.IsRegular
      (Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span (Set.range relations)))))
      (List.ofFn fun i : Fin c ↦
        algebraMap (MvPolynomial (Fin n) R)
          (Localization.AtPrime (q.comap (Ideal.Quotient.mk (Ideal.span (Set.range relations)))))
          (relations i)) := by
  classical
  let Q := q.comap (Ideal.Quotient.mk (Ideal.span (Set.range relations)))
  have hQ : Ideal.span (Set.range relations) ≤ Q := by
    intro x hx
    change Ideal.Quotient.mk (Ideal.span (Set.range relations)) x ∈ q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact q.zero_mem
  obtain ⟨R₀, hR₀, f₀, hcoeff, hf₀⟩ :=
    exists_finiteType_subring_relativeGlobalCompleteIntersection R n c relations h
  have hf : relations = fun i ↦ MvPolynomial.map R₀.subtype (f₀ i) := by
    funext i
    ext d
    simpa only [MvPolynomial.coeff_map, Subring.subtype_apply] using hcoeff i d
  have hweak : RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime Q)
      ((List.ofFn relations).map
        (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime Q))) := by
    rw [congrArg List.ofFn hf]
    apply RingTheory.Sequence.isWeaklyRegular_polynomial_local_of_finiteType_subrings
      R₀ hR₀ f₀ Q
    intro B hB hft
    let : Algebra R₀ B := (Subring.inclusion hB).toAlgebra
    have : Algebra.FiniteType ℤ B := hft
    have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
    let fB := fun i ↦ MvPolynomial.map (Subring.inclusion hB) (f₀ i)
    have hfB : IsRelativeGlobalCompleteIntersectionPresentation fB :=
      (relativeGlobalCompleteIntersection_baseChange R₀ B n c f₀).2 hf₀
    have hQB : Ideal.span (Set.range fB) ≤ Q.comap (MvPolynomial.map B.subtype) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change MvPolynomial.map B.subtype (fB i) ∈ Q
      have hmap : MvPolynomial.map B.subtype (fB i) = relations i := by
        rw [hf]
        dsimp [fB]
        rw [MvPolynomial.map_map]
        rfl
      rw [hmap]
      exact hQ (Ideal.subset_span ⟨i, rfl⟩)
    exact (isRegular_localization_of_relativeCompleteIntersection_of_noetherian
      fB hfB (Q.comap (MvPolynomial.map B.subtype)) hQB).toIsWeaklyRegular
  have hmem : ∀ x ∈ (List.ofFn relations).map
      (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime Q)),
      x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (hQ (Ideal.subset_span ⟨i, rfl⟩))
  simpa only [List.map_ofFn, Function.comp_def] using
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr hweak

end Algebra
