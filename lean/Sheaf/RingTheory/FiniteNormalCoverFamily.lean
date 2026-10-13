module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.Paper.NormalLocusOpen

@[expose] public section

universe u v

/-- A finite family whose normal fibers cover every prime of the base.
Source: Stacks Project, Algebra, Tag 0333, reverse implication, paragraphs defining
`Z_C` and extracting a finite collection; Tag 0332 for openness of the normal locus.
(blueprint: lem-weil-pbc-finite-normal-cover-family)

Proof: Choose the nonzero f of hAway. The local criterion for normality makes A_f
normal. For each finite intermediate C contained in the integral closure, C_f is
integral over A_f inside their common fraction field K, hence C_f = A_f. The ring C
is a Noetherian domain and its normal locus is open by Tag 0332. Since C is integral
over A, Spec C -> Spec A is closed, so the image Z_C of the non-normal locus is closed.
For each maximal m, hLocal supplies a C for which m is outside Z_C. Each prime p is
contained in a maximal m. If p belonged to that Z_C, specialization-closedness would
put m in Z_C too. Therefore the opens Spec A \ Z_C cover Spec A. Quasi-compactness
extracts finitely many C, forming s. Every member satisfies the original finiteness
and containment conditions. For any prime p, membership in one of these opens says
exactly that every prime of the corresponding C contracting to p has normal
localization, which is the final clause below. -/
theorem exists_finite_normal_cover_family (A : Type u) (K : Type v)
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (hAway : ∃ f : A, f ≠ 0 ∧
      ∀ (p : Ideal (Localization.Away f)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hLocal : ∀ (m : Ideal A) [m.IsMaximal],
      ∃ B : Subalgebra A K, B ≤ integralClosure A K ∧ Module.Finite A B ∧
        ∀ (q : Ideal B) [q.IsPrime], Ideal.comap (algebraMap A B) q = m →
          IsIntegrallyClosed (Localization.AtPrime q)) :
    ∃ s : Finset (Subalgebra A K),
      (∀ C ∈ s, C ≤ integralClosure A K ∧ Module.Finite A C) ∧
      ∀ (p : Ideal A) [p.IsPrime], ∃ C ∈ s,
        ∀ (q : Ideal C) [q.IsPrime], Ideal.comap (algebraMap A C) q = p →
          IsIntegrallyClosed (Localization.AtPrime q) := by
  sorry
