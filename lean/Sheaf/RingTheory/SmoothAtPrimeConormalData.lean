module
public import Sheaf.RingTheory.SingularIdeal
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
@[expose] public section
universe u
namespace Algebra
/-- The smooth localization and prescribed conormal basis data exist.
Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07C6.
(blueprint: lem-weil-pbc-smooth-at-prime-free-conormal-basis-conormal-data)
The proof chooses a smooth principal neighbourhood, selects a residue-field basis
from the given generators, and spreads it after shrinking; this is the conormal
part of Tag 07C6. -/
theorem exists_smoothAtPrime_conormal_data
    (R : Type u) [CommRing R] (n m : ℕ)
    (f : Fin m → MvPolynomial (Fin n) R)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
    (hs : Algebra.IsSmoothAtPrime R q) :
    ∃ (a : MvPolynomial (Fin n) R),
      Ideal.Quotient.mk (Ideal.span (Set.range f)) a ∉ q.asIdeal ∧
      ∃ (V : Finset (Fin m)) (c : ℕ),
        V.card = c ∧ c ≤ min n m ∧
        Algebra.Smooth R (Localization.Away
          (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)) ∧
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
                    Ideal.subset_span ⟨(e j).1, rfl⟩⟩)) := by
  sorry
end Algebra
