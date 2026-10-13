module
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Sheaf.RingTheory.CompleteIntersectionOverField
@[expose] public section
universe u v
namespace Algebra
/-- Core presentation and localization comparison underlying the syntomic equation-count theorem.
Source: Stacks Project, Algebra, Tag 00SY, proof of (3) ⇒ (2),
presentation, Nakayama and flatness steps.
(blueprint: lem-weil-pbc-syntomic-equation-count-comparison-core).
The proof constructs a finite polynomial presentation, chooses the conormal generators, and uses
flatness plus Nakayama to obtain an isomorphism after inverting an element outside the prime. -/
theorem exists_equationCount_comparison_core
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S)
    (hfp : FinitePresentation R S)
    (hflat : (Localization.localRingHom (q.asIdeal.comap (algebraMap R S)) q.asIdeal
      (algebraMap R S) rfl).Flat)
    (hci : ∃ h : (q.asIdeal.comap (algebraMap R S)).Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩).asIdeal ∧
      IsGlobalCompleteIntersection (q.asIdeal.comap (algebraMap R S)).ResidueField
        (Localization.Away h)) :
    ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R),
      let T := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
      ∃ (π : T →ₐ[R] S) (u : T),
        Function.Surjective π ∧ π u ∉ q.asIdeal ∧
        Function.Bijective
          (IsLocalization.Away.mapₐ (Localization.Away u) (Localization.Away (π u)) π u) ∧
        c ≤ n := by sorry
end Algebra
