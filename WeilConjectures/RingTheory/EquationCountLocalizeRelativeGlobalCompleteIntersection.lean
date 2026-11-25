/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersection
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
import WeilConjectures.RingTheory.EquationCountLocalizePresentation
import WeilConjectures.RingTheory.EquationCountLocalizeRGCI

/-!
# Localizing an equation-count presentation

## Implementation details

The enlarged presentation is indexed by `Option`, adding one variable and one equation. Besides
the ring-map predicate `IsRelativeGlobalCompleteIntersection`, which only asserts the existence of
some presentation, the main theorem records the fibre condition for this specific presentation.

## References

* Stacks Project, Algebra, Lemmas 00ST (3) and 00QH
-/

@[expose] public section

universe u

namespace Algebra

/-- At a prime `q` of `S = R[x_1, …, x_n] ⧸ (f_1, …, f_c)` where the fibre has local dimension
`n - c`, there is a polynomial `h` with image `g ∉ q` such that the quotient `T` of
`R[x, z]` by the `f_i` and `h z - 1` is a relative global complete intersection, every nonempty
fibre of this presentation has dimension `(n + 1) - (c + 1)`, and `T ≃ S_g` with `z ↦ g⁻¹`. -/
theorem exists_localization_relativeGlobalCompleteIntersection
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
    (hdim :
      let S := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
      let p := PrimeSpectrum.comap (algebraMap R S) q
      c ≤ n ∧ topologicalKrullDimAt
        (PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩) = (n - c : ℕ)) :
    ∃ h : MvPolynomial (Fin n) R,
      let S := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
      let g : S := Ideal.Quotient.mk _ h
      g ∉ q.asIdeal ∧
      let relations : Option (Fin c) → MvPolynomial (Option (Fin n)) R :=
        Option.elim' (MvPolynomial.rename some h * MvPolynomial.X none - 1)
          (fun i ↦ MvPolynomial.rename some (f i))
      let T := MvPolynomial (Option (Fin n)) R ⧸ Ideal.span (Set.range relations)
      IsRelativeGlobalCompleteIntersection (algebraMap R T) ∧
        (∀ (p : Ideal R) (_hp : p.IsPrime),
          letI : p.IsPrime := _hp
          Nontrivial (p.Fiber T) →
            c + 1 ≤ n + 1 ∧
              topologicalKrullDim (PrimeSpectrum (p.Fiber T)) = (n + 1 - (c + 1) : ℕ)) ∧
        ∃ e : T ≃ₐ[R] Localization.Away g,
          (∀ i : Fin n,
            e (Ideal.Quotient.mk _ (MvPolynomial.X (some i))) =
              algebraMap S (Localization.Away g) (Ideal.Quotient.mk _ (MvPolynomial.X i))) ∧
          e (Ideal.Quotient.mk _ (MvPolynomial.X none)) =
            IsLocalization.Away.invSelf g := by
  obtain ⟨h, hh⟩ := localized_presentation_is_relativeGlobalCompleteIntersection R n c f q hdim
  obtain ⟨e, hevars, henew⟩ := exists_localization_presentation R n c f h
  refine ⟨h, ?_⟩
  exact ⟨hh.1, hh.2.1, hh.2.2, ⟨e, hevars, henew⟩⟩

end Algebra
