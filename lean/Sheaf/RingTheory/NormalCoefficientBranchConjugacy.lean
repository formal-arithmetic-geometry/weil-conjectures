module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Normal coefficient automorphisms conjugate normalized branches

Source: Stacks Project, more-algebra.tex, Tag 09EU (lemma-galois-relative), with the
branch rings of Tag 09EM (remark-construction) and the invariant-power correction
for inseparable normal extensions (blueprint: lem-sfb-normal-coefficient-branch-conjugacy).
-/

@[expose] public section

universe uA uB uK uL uN

open scoped TensorProduct

namespace Algebra

/-- Normal coefficient automorphisms act on the reduced tensor algebra and its two
integral closures, transitively on upper maximal ideals, and conjugate the local branch maps.
Source: Stacks Project, more-algebra.tex, Tags 09EU and 09EM; localization is Algebra, Tag 00CO
(blueprint: lem-sfb-normal-coefficient-branch-conjugacy).

The three monoid homomorphisms are the actions, uniquely specified by their displayed
restriction equations. The embedding `i` is likewise specified by its value in the reduced
tensor algebra. The primes `n,n'` are exactly the contractions, and `localRingHom` is the
canonical local branch map. The last two equations give the isomorphisms on fractions.

Proof:
1. Apply lem-sfb-dvr-algebraic-normalization-structure, case (a). The reduced tensor algebra
   is a nonempty finite product of fields, so both field maps into it are injective. An
   A-integral element becomes B-integral, giving i. Every maximal ideal of the upper integral
   closure contracts to the maximal ideal of B by integral-maximal-contracts-maximal. The PID B
   is integrally closed by lem-weil-pbc-pid-noetherian-normal.
2. The coefficient automorphism group is finite by finite-extension-finitely-many-embeddings.
   Tensor pushout universality constructs 1 tensor sigma and its inverse. They preserve
   nilpotents and monic equations, so descend to the reduction and restrict to both integral
   closures. Uniqueness gives the group laws and compatibility with i.
3. If two maximal ideals have different orbits, use lem-pc-crt-ideal-quotient-product on the
   two finite disjoint orbits to choose b with residues zero and one. The product of all
   sigma(b) is invariant and still has these two residues.
4. By lem-sfb-normal-tensor-invariant-powers, some positive power of that invariant is in L.
   It is B-integral and hence in B. Its residues would put the same element of B both inside
   and outside the maximal ideal of B, a contradiction. This uses invariant powers, never
   the false fixed-field identity for an inseparable normal extension.
5. Choose sigma carrying q to q'. Compatibility with i carries the contraction n to n'.
   Localize i at these contractions. A fraction belongs to the localized prime exactly when
   its numerator belongs to the prime, so both canonical branch maps are local.
6. Send b/s to sigma(b)/sigma(s). The ideal equalities preserve allowed denominators, and
   applying sigma to u(bs'-b's)=0 proves well-definedness. The inverse uses sigma inverse;
   the numerator test proves locality. Both routes around the square send r/s to
   sigma(r)/sigma(s), so the square commutes. No completeness, henselianity, separability,
   locality of the lower integral closure, or equality of n and n' is used. -/
theorem normalCoefficientBranchConjugacy
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (N : Type uN)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field N]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hAB : Function.Injective (algebraMap A B))
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra K N] [Algebra A N] [IsScalarTower A K N]
    [FiniteDimensional K N] [Normal K N] :
    ∃ (i : integralClosure A N →+*
        integralClosure B ((L ⊗[K] N) ⧸ nilradical (L ⊗[K] N)))
      (ρN : (N ≃ₐ[K] N) →* (integralClosure A N ≃+* integralClosure A N))
      (ρE : (N ≃ₐ[K] N) →*
        (((L ⊗[K] N) ⧸ nilradical (L ⊗[K] N)) ≃+*
          ((L ⊗[K] N) ⧸ nilradical (L ⊗[K] N))))
      (ρC : (N ≃ₐ[K] N) →*
        (integralClosure B ((L ⊗[K] N) ⧸ nilradical (L ⊗[K] N)) ≃+*
          integralClosure B ((L ⊗[K] N) ⧸ nilradical (L ⊗[K] N)))),
      (∀ r : integralClosure A N,
        (i r).val = Ideal.Quotient.mk (nilradical (L ⊗[K] N)) (1 ⊗ₜ[K] r.val)) ∧
      (∀ (σ : N ≃ₐ[K] N) (r : integralClosure A N), (ρN σ r).val = σ r.val) ∧
      (∀ (σ : N ≃ₐ[K] N) (l : L) (x : N),
        ρE σ (Ideal.Quotient.mk (nilradical (L ⊗[K] N)) (l ⊗ₜ[K] x)) =
          Ideal.Quotient.mk (nilradical (L ⊗[K] N)) (l ⊗ₜ[K] σ x)) ∧
      (∀ (σ : N ≃ₐ[K] N)
        (c : integralClosure B ((L ⊗[K] N) ⧸ nilradical (L ⊗[K] N))),
        (ρC σ c).val = ρE σ c.val) ∧
      ∀ (q q' : PrimeSpectrum
        (integralClosure B ((L ⊗[K] N) ⧸ nilradical (L ⊗[K] N)))),
        q.asIdeal.IsMaximal → q'.asIdeal.IsMaximal →
        ∃ (σ : N ≃ₐ[K] N) (n n' : PrimeSpectrum (integralClosure A N))
          (hn : n.asIdeal = q.asIdeal.comap i) (hn' : n'.asIdeal = q'.asIdeal.comap i),
          Ideal.map (ρC σ).toRingHom q.asIdeal = q'.asIdeal ∧
          Ideal.map (ρN σ).toRingHom n.asIdeal = n'.asIdeal ∧
          ∃ (hN : ∀ s : n.asIdeal.primeCompl, ρN σ s ∈ n'.asIdeal.primeCompl)
            (hC : ∀ s : q.asIdeal.primeCompl, ρC σ s ∈ q'.asIdeal.primeCompl)
            (eN : Localization.AtPrime n.asIdeal ≃+* Localization.AtPrime n'.asIdeal)
            (eC : Localization.AtPrime q.asIdeal ≃+* Localization.AtPrime q'.asIdeal),
            IsLocalHom eN.toRingHom ∧ IsLocalHom eC.toRingHom ∧
            eC.toRingHom.comp (Localization.localRingHom n.asIdeal q.asIdeal i hn) =
              (Localization.localRingHom n'.asIdeal q'.asIdeal i hn').comp eN.toRingHom ∧
            (∀ (b : integralClosure A N) (s : n.asIdeal.primeCompl),
              eN (IsLocalization.mk' (Localization.AtPrime n.asIdeal) b s) =
                IsLocalization.mk' (Localization.AtPrime n'.asIdeal) (ρN σ b)
                  ⟨ρN σ s, hN s⟩) ∧
            (∀ (b : integralClosure B ((L ⊗[K] N) ⧸ nilradical (L ⊗[K] N)))
              (s : q.asIdeal.primeCompl),
              eC (IsLocalization.mk' (Localization.AtPrime q.asIdeal) b s) =
                IsLocalization.mk' (Localization.AtPrime q'.asIdeal) (ρC σ b)
                  ⟨ρC σ s, hC s⟩) := by
  sorry

end Algebra
