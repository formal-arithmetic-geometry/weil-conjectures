module
public import Sheaf.RingTheory.SingularIdeal
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import Sheaf.RingTheory.SmoothAtPrimeConormalData
@[expose] public section
universe u
namespace Algebra
/-- After the conormal basis has been spread on a smooth localization, the
Kähler differential module is free of complementary rank.
Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07C6.
(blueprint: lem-weil-pbc-smooth-at-prime-free-conormal-basis-differential-data)
The hypothesis supplies the prescribed conormal basis; the proof then spreads a
basis of the finite projective differential module at the prime and takes a
common principal shrink. -/
theorem exists_smoothAtPrime_differential_data
    (R : Type u) [CommRing R] (n m : ℕ)
    (f : Fin m → MvPolynomial (Fin n) R)
    (a : MvPolynomial (Fin n) R)
    (V : Finset (Fin m)) (c : ℕ)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
    (ha : Ideal.Quotient.mk (Ideal.span (Set.range f)) a ∉
      q.asIdeal)
    (hcard : V.card = c) (hbound : c ≤ min n m)
    (hsm : Algebra.Smooth R (Localization.Away
      (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))) :
    (∃ (e : Fin c ≃ V),
      ∃ b : Module.Basis (Fin c)
          (Localization.Away
            (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))
          (LocalizedModule.Away
            (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)
            (Ideal.span (Set.range f)).Cotangent),
        ∀ j : Fin c,
          b j = LocalizedModule.mkLinearMap
            (Submonoid.powers
              (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))
            (Ideal.span (Set.range f)).Cotangent
            ((Ideal.span (Set.range f)).toCotangent
              ⟨f (e j).1,
                Ideal.subset_span ⟨(e j).1, rfl⟩⟩)) →
    Nonempty (Module.Basis (Fin (n - c))
      (Localization.Away
        (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))
      (KaehlerDifferential R
        (Localization.Away
          (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)))) := by
  sorry
end Algebra
