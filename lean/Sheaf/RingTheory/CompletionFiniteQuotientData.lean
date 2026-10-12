module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.RingTheory.CompletionFiniteExtension

@[expose] public section

universe u
open Polynomial TensorProduct
namespace AdicCompletion

/-! # Finite local completion comparison for a monic quotient

Source: Stacks Project, Algebra Tag 07N9 (lemma-completion-finite-extension),
used in More on Algebra Tag 07PR (lemma-helper-G-ring).
(blueprint: lem-weil-pbc-completion-finite-quotient-data). -/

/-- The completed-base map and tensor comparison in the finite local quotient case.
Source: Stacks Project, Algebra Tag 07N9 (lemma-completion-finite-extension),
and More on Algebra Tag 07PR (lemma-helper-G-ring).
(blueprint: lem-weil-pbc-completion-finite-quotient-data).

Proof:
1. The monic polynomial `X ^ p - C f` has positive degree `p`. Its quotient is free
   with basis `1, z, ..., z^(p-1)` by lem-weil-pbc-monic-quotient-free, hence finite
   and integral over R by lem-weil-pbc-finite-algebra-is-integral.
2. Integrality contracts the maximal ideal n to a maximal ideal of R, necessarily m,
   by lem-weil-pbc-integral-maximal-contracts-maximal. Every prime over m is maximal
   by lem-weil-pbc-integral-prime-over-maximal-maximal, hence is n since S is local.
3. In a local ring, all elements outside the maximal ideal are units. Therefore
   localization at that ideal is an isomorphism (lem-weil-pbc-localization-units-or-zero).
   It carries each ideal power to its extension, yielding compatible quotient
   isomorphisms and, coordinatewise, completion isomorphisms for R and S. Under these
   identifications Localization.localRingHom is the original coefficient map phi:
   both send r/t to phi(r)/phi(t).
4. Apply completion_finite_extension (lem-weil-pbc-completion-finite-extension) at m.
   The set of primes over m consists of n, so evaluating its product at n is an
   isomorphism. Transport the completed-base map through the isomorphisms of step 3;
   its coordinate formula becomes precisely the displayed formula for g. Transport
   the tensor isomorphism in the same way and forget to a ring equivalence gamma.
   Its S-linearity gives gamma(a tensor c) = gamma(a tensor 1) * iotaS(c), while
   its completed-base compatibility gives gamma(a tensor 1) = g(a). This proves
   the pure-tensor formula. No completed polynomial presentation is asserted here. -/
theorem completion_finite_quotient_data
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p : ℕ) (hp : 1 ≤ p) (f : R) [IsLocalRing (AdjoinRoot (X ^ p - C f))] :
    let S := AdjoinRoot (X ^ p - C f)
    let m := IsLocalRing.maximalIdeal R
    let n := IsLocalRing.maximalIdeal S
    let Rhat := AdicCompletion m R
    let Shat := AdicCompletion n S
    let ι := algebraMap R Rhat
    let ιS := algebraMap S Shat
    let φ := algebraMap R S
    ∃ g : Rhat →+* Shat,
      (∀ (a : Rhat) (k : ℕ) (r : R),
        evalₐ m k a = Ideal.Quotient.mk (m ^ k) r →
        evalₐ n k (g a) = Ideal.Quotient.mk (n ^ k) (φ r)) ∧
      (∃ γ : (Rhat ⊗[R] S) ≃+* Shat,
        ∀ (a : Rhat) (c : S), γ (a ⊗ₜ[R] c) = g a * ιS c) := by
  sorry

end AdicCompletion
