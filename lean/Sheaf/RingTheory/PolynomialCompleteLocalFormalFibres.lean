import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Sheaf.RingTheory.GRing

universe u

namespace Polynomial

/-- The completion map at a maximal ideal over the maximal ideal of a complete local
Noetherian ring is regular. Source: Stacks Project, More on Algebra, proof of
Proposition 07PV, paragraphs 2--5
(blueprint: lem-weil-pbc-polynomial-complete-local-formal-fibres).
Proof (the seven steps of the node), with T = S[x]_Q and C its completion:
1. S[x] and T are Noetherian, so T → C is flat (lem-weil-pbc-noetherian-completion-flat)
with Noetherian fibres (lem-weil-pbc-fibre-ring-noetherian); the primes of T are the rT,
r ⊆ Q, and it remains to show C ⊗_{S[x]} κ(r) geometrically regular over κ(r).
2. With p = r ∩ S and A = S/p (lem-weil-pbc-complete-local-quotient), pass to the
complete local domain A, the images of Q and r (r ∩ A = 0), using
lem-weil-pbc-localization-at-prime-of-quotient and lem-weil-pbc-local-completion-quotient.
3. Choose a regular complete local subring A₀ ⊆ A with A finite over A₀
(lem-weil-pbc-complete-local-domain-finite-over-regular); Q₀ = Q ∩ A₀[x] is maximal,
A₀[x] → A[x] is quasi-finite at Q, and lem-weil-pbc-formal-fibre-quasi-finite-ascent
reduces to the formal fibre of A₀[x] at Q₀ over r₀ = r ∩ A₀[x].
4. A₀[x] is regular (lem-weil-pbc-regular-ring-smooth-ascent), so C₀ = (A₀[x]_{Q₀})^∧ is
regular (lem-weil-pbc-completion-regular-local), and so are its localizations.
5. Characteristic 0, r₀ = 0: the fibre is a localization of C₀, hence regular, and
geometrically regular as there are no nontrivial purely inseparable extensions.
6. Characteristic 0, r₀ ≠ 0: r₀K₀[x] = (f), the fibre is R/fR with R a localization of
C₀; d/dx extends (lem-weil-pbc-derivation-extends) with D(f) = f' a unit mod f, so R/fR
is regular (lem-weil-pbc-hypersurface-derivation-regular).
7. Characteristic p: A₀ ≅ k[[X₁, …, X_d]]; r₀ = 0 by lem-weil-pbc-helper-g-ring-char-p,
r₀ ≠ 0 by lem-weil-pbc-another-helper-g-ring. Steps 3, 2, 1 conclude. -/
theorem completeLocalFormalFibres
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S]
    (Q : Ideal (Polynomial S)) [Q.IsMaximal]
    (hQ : Q.comap (Polynomial.C : S →+* Polynomial S) = IsLocalRing.maximalIdeal S) :
    RingHom.IsRegular
      (algebraMap (Localization.AtPrime Q)
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
          (Localization.AtPrime Q))) := by
  sorry

end Polynomial
