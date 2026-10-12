module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

universe u v

/-- Finite supremum patching for a finite family of locally normal intermediate algebras.
Source: Stacks Project, Algebra, Tag 0333, the finite-generation and final localization
paragraphs. (blueprint: lem-weil-pbc-finite-normal-sup)
For a finite family of intermediate algebras, their supremum in `Subalgebra A K` is finite
over `A`, remains inside the integral closure, and its prime localizations are the normal
localizations supplied by the family.  The algebraic finite-generation and localization
glue is isolated here so the compactness extraction is independent. -/
theorem finite_normal_sup (A : Type u) (K : Type v)
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (s : Finset (Subalgebra A K)) (S : Subalgebra A K)
    (hS : S = s.sup (fun C : Subalgebra A K => C))
    (hs : ∀ C ∈ s, C ≤ integralClosure A K ∧ Module.Finite A C)
    (hn : ∀ (q : Ideal S) [q.IsPrime],
      IsIntegrallyClosed (Localization.AtPrime q)) :
    ∃ B : Subalgebra A K, B ≤ integralClosure A K ∧ Module.Finite A B ∧
      ∀ (q : Ideal B) [q.IsPrime], IsIntegrallyClosed (Localization.AtPrime q) := by
  sorry
