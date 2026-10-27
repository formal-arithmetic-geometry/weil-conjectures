module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.FiniteTypeGRing
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.PairHenselization
import WeilConjectures.RingTheory.HenselizationPairGRing
import WeilConjectures.RingTheory.PairHenselizationNoetherianCompletion
import WeilConjectures.RingTheory.HenselianPairApproximation

/-!
# Algebraization from a power-split continuous conormal map

Source: Stacks Project, Restricted Power Series, Proposition 0GAT and Lemma 0GAJ(3)
(blueprint: lem-per-g-ring-rig-smooth-algebraization).

The normalization of the conormal map is expressed at every finite adic level:
if a polynomial represents an element of the relation ideal modulo the nth power,
its partial derivatives represent the coordinates of the conormal map modulo that
power in the quotient. This specifies the continuous derivatives, including on
relations which are not polynomials.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace RingTheory

/-- Algebraization of a completed polynomial quotient with power-split conormal map.
Source: Stacks Project, Proposition 0GAT, using Lemma 0GAJ(3)
(blueprint: lem-per-g-ring-rig-smooth-algebraization).

Here `hδ` specifies the continuous derivative map by polynomial approximation at
all adic levels. The quotient is separated by `hcomplete`, so these congruences
uniquely determine each coordinate of the map on every conormal class.

Proof:
1. Put S = R[x₁,...,xᵣ]. By lem-weil-pbc-finite-type-over-g-ring it is a
   Noetherian G-ring, and lem-weil-pbc-adic-completion-noetherian makes its
   completion P Noetherian. Choose finite generators g of J. Apply the maximal
   element clause of lem-weil-pbc-noetherian-finite-module-acc to finitely
   generated submodules of the kernel of the row g. A maximal one contains
   every kernel vector, since adjoining an omitted vector would enlarge it.
   Thus choose a finite syzygy matrix K, giving an exact presentation of B.
2. The power-splitting hypothesis and lem-per-rig-smooth-presentation-perturbation
   give a precision N ≥ 1. Form the pair henselization H of (S, IS) using
   lem-weil-pbc-pair-henselization. By lem-weil-pbc-henselization-pair-g-ring
   and lem-weil-pbc-henselization-noetherian-completion, H is a Noetherian
   G-ring, (H, IH) is henselian, and its completion is canonically P.
3. Apply lem-weil-pbc-henselian-pair-approximation to the finite equations
   Σ Uⱼ Vⱼₗ = 0 satisfied by g and K in P. Obtain exact solutions u, v in H
   congruent to g, K modulo IᴺP. Their images g', K' form a complex and meet
   every congruence required by the perturbation lemma.
4. That lemma identifies B with P/(g'). For Q = (u) in H its extension to P
   is exactly (g'). Apply lem-per-henselian-equations-algebraization to R, S,
   H and Q. It gives a finite type R-algebra C whose completion is P/(g').
   Compose these R-algebra isomorphisms to identify the completion of C with B.
-/
theorem gRing_rigSmooth_algebraization
    (R : Type u) [CommRing R] (hR : IsGRing R) (I : Ideal R) (r : ℕ)
    (J : Ideal (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial (Fin r) R))
      (MvPolynomial (Fin r) R)))
    (hcomplete : IsAdicComplete I
      (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial (Fin r) R))
        (MvPolynomial (Fin r) R) ⧸ J))
    (δ : J.Cotangent →ₗ[AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial (Fin r) R))
        (MvPolynomial (Fin r) R) ⧸ J]
      (Fin r → AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial (Fin r) R))
        (MvPolynomial (Fin r) R) ⧸ J))
    (hδ : ∀ (n : ℕ) (f : J) (p : MvPolynomial (Fin r) R),
      AdicCompletion.evalₐ _ n f.val = Ideal.Quotient.mk (_ ^ n) p →
      ∀ i : Fin r,
        δ (J.toCotangent f) i -
          Ideal.Quotient.mk J
            (algebraMap (MvPolynomial (Fin r) R) _ (MvPolynomial.pderiv i p)) ∈
              (I ^ n).map (algebraMap R _))
    (hsplit : ∃ c : ℕ, ∀ a : R, a ∈ I ^ c →
      ∃ h : (Fin r → AdicCompletion
        (I.map (MvPolynomial.C : R →+* MvPolynomial (Fin r) R))
          (MvPolynomial (Fin r) R) ⧸ J) →ₗ[
        AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial (Fin r) R))
          (MvPolynomial (Fin r) R) ⧸ J] J.Cotangent,
        ∀ x : J.Cotangent, h (δ x) = a • x) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C),
      RingHom.FiniteType (algebraMap R C) ∧
        Nonempty (AdicCompletion (I.map (algebraMap R C)) C ≃ₐ[R]
          (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial (Fin r) R))
            (MvPolynomial (Fin r) R) ⧸ J)) := by
  sorry

end RingTheory
