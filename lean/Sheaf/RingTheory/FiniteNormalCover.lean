module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

universe u v

/-- Finite normal cover extracted from the local normal approximation hypotheses.
Source: Stacks Project, Algebra, Tag 0333, the compactness patching paragraph.
(blueprint: lem-weil-pbc-finite-normal-cover)
The closed non-normal loci attached to the finite intermediate algebras supplied at
maximal ideals have open complements covering `Spec A`.  Quasi-compactness of `Spec A`
therefore gives finitely many such algebras.  The resulting finite family is recorded here;
the topological and localization arguments are postponed to the theorem using this family. -/
theorem exists_finite_normal_cover (A : Type u) (K : Type v)
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (hAway : ∃ f : A, f ≠ 0 ∧
      ∀ (p : Ideal (Localization.Away f)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hLocal : ∀ (m : Ideal A) [m.IsMaximal],
      ∃ B : Subalgebra A K, B ≤ integralClosure A K ∧ Module.Finite A B ∧
        ∀ (q : Ideal B) [q.IsPrime], Ideal.comap (algebraMap A B) q = m →
          IsIntegrallyClosed (Localization.AtPrime q)) :
    ∃ s : Finset (Subalgebra A K), ∃ S : Subalgebra A K,
      S = s.sup (fun C : Subalgebra A K => C) ∧
      (∀ C ∈ s, C ≤ integralClosure A K ∧ Module.Finite A C) ∧
      ∀ (q : Ideal S) [q.IsPrime],
        IsIntegrallyClosed (Localization.AtPrime q) := by
  sorry
