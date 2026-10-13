module
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
@[expose] public section
universe u v
namespace Algebra
/-- Dimension calculation for a comparison quotient at the canonical fibre prime.
Source: Stacks Project, Algebra, Tags 00SY and 00P2.
(blueprint: lem-weil-pbc-syntomic-equation-count-comparison-dimension).
Given the comparison presentation and its localization isomorphism, the fibre dimension at the
canonical prime is the codimension n-c. -/
theorem equationCount_comparison_dimension
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) {n c : ℕ} {f : Fin c → MvPolynomial (Fin n) R}
    (π : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) →ₐ[R] S)
    (u : MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
    (hsurj : Function.Surjective π) (hu : π u ∉ q.asIdeal)
    (hbij : Function.Bijective
      (IsLocalization.Away.mapₐ (Localization.Away u) (Localization.Away (π u)) π u))
    (hle : c ≤ n) :
    topologicalKrullDimAt
      (PrimeSpectrum.preimageEquivFiber R
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
        ((q.comap π.toRingHom).comap
          (algebraMap R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))))
        ⟨q.comap π.toRingHom, rfl⟩) = (n - c : ℕ) := by sorry
end Algebra
