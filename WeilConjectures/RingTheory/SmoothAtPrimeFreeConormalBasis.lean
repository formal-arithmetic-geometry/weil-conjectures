/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.RingTheory.SmoothAtPrimeConormalData
import WeilConjectures.RingTheory.SmoothAtPrimeDifferentialData

/-!
# Free conormal basis near a smooth prime

Near a smooth prime of a quotient of a polynomial ring, some of the defining equations form a
basis of the localized conormal module, and the localized module of differentials is free of
complementary rank.

## References

* [Stacks, Tag 07C6]
-/

@[expose] public section

universe u

namespace Algebra

/-- Near a smooth prime of a polynomial quotient, selected defining equations form a
basis of the localized conormal module, and the differentials are free of complementary rank. -/
theorem exists_smoothAtPrime_free_conormal_basis
    (R : Type u) [CommRing R] (n m : ℕ)
    (f : Fin m → MvPolynomial (Fin n) R)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
    (hs : Algebra.IsSmoothAtPrime R q) :
    ∃ (a : MvPolynomial (Fin n) R),
      Ideal.Quotient.mk (Ideal.span (Set.range f)) a ∉ q.asIdeal ∧
      ∃ (V : Finset (Fin m)) (c : ℕ),
        V.card = c ∧ c ≤ min n m ∧
        Algebra.Smooth R
          (Localization.Away
            (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)) ∧
        (∃ (e : Fin c ≃ V),
          ∃ b : Module.Basis (Fin c)
              (Localization.Away
                (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))
              (LocalizedModule.Away
                (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)
                (Ideal.span (Set.range f)).Cotangent),
            ∀ j : Fin c,
              b j =
                LocalizedModule.mkLinearMap
                  (Submonoid.powers
                    (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))
                  (Ideal.span (Set.range f)).Cotangent
                  ((Ideal.span (Set.range f)).toCotangent
                    ⟨f (e j).1,
                      Ideal.subset_span ⟨(e j).1, rfl⟩⟩)) ∧
        Nonempty (Module.Basis (Fin (n - c))
          (Localization.Away
            (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))
          (KaehlerDifferential R
            (Localization.Away
              (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)))) := by
  rcases exists_smoothAtPrime_conormal_data R n m f q hs with
    ⟨a, ha, V, c, hcard, hbound, hsm, hb⟩
  obtain ⟨a', ha', hsm', hb', hdiff⟩ :=
    exists_smoothAtPrime_differential_data R n m f a V c q ha hcard hbound hsm hb
  exact ⟨a', ha', V, c, hcard, hbound, hsm', hb', hdiff⟩

end Algebra
