/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuAdmissibleSubalgebra
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Algebra.MvPolynomial.Basic
import WeilConjectures.RingTheory.PopescuFlatCoordinatesA0
import WeilConjectures.RingTheory.PopescuFlatCoordinatesGivenAdmissible

/-!
# Flat coordinates adapted to an Artinian subalgebra

We choose an admissible subalgebra containing a finite set, together with flat polynomial
coordinates whose residue differentials span its differentials.

## Implementation details

This is the coordinate-construction part of the proof of Stacks Tag 07FH, not the essentially
smooth factorization; no quotient factorization or étaleness is asserted.

## References

* [Stacks, Tag 07FH] (proof, through property (1))
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- Choose an admissible subalgebra containing a finite set and flat polynomial coordinates
whose residue differentials span its differentials. -/
theorem exists_popescu_flat_coordinates
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hreg : IsGeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime]
    (n : ℕ) (hn : 1 ≤ n)
    (E : Finset (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) :
    ∃ (A : Subalgebra k (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) (_ : IsLocalRing A),
      A.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      IsLocalRing.maximalIdeal A = Ideal.comap A.val.toRingHom
        ((q.map (algebraMap Λ (Localization.AtPrime q))).map
          (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      (∀ e ∈ E, e ∈ A) ∧
      ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
        (ψ : Localization.AtPrime (q.comap φ.toRingHom) →+* Localization.AtPrime q),
        ψ.comp (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (q.comap φ.toRingHom))) =
          (algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom ∧
        q.map (algebraMap Λ (Localization.AtPrime q)) =
          (q.comap φ.toRingHom).map
            ((algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom) ∧
        ψ.Flat ∧
        ∃ a : Fin m → A,
          (∀ j, (a j : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
              (algebraMap Λ (Localization.AtPrime q) (φ (MvPolynomial.X j)))) ∧
          Submodule.span (IsLocalRing.ResidueField A)
            (Set.range (fun j ↦ KaehlerDifferential.D k (IsLocalRing.ResidueField A)
              (IsLocalRing.residue A (a j)))) = ⊤ := by
  obtain ⟨A₀, hA₀loc, hA₀, hE⟩ :=
    exists_popescu_admissible_containing_finset k Λ p hp hreg q n hn E
  obtain ⟨A, hAloc, hA, hmA, hle, hcoords⟩ :=
    exists_popescu_flat_coordinates_given_admissible k Λ p hp hreg q n hn A₀ hA₀loc hA₀
  exact ⟨A, hAloc, hA, hmA, (fun e he ↦ hle (hE e he)), hcoords⟩

end Algebra
