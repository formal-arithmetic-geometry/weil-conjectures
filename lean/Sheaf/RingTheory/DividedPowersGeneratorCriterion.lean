module

public import Mathlib.RingTheory.DividedPowers.Basic

/-!
# Checking divided-power axioms on ideal generators

Source: Stacks Project, `dpa.tex`, Tag 07GP, Lemma `lemma-check-on-generators`,
conditions (a), (b) and conclusion (blueprint: lem-sfb-pd-generator-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace DividedPowers

/-- Multiplication and iteration need only be checked on a set of ideal generators.

Source: Stacks Project, Tag 07GP, Lemma `lemma-check-on-generators`, and Tag 07GL,
Definition `definition-divided-powers` (blueprint: lem-sfb-pd-generator-criterion).

The functions `δ n` have domain `J`. The range condition says that positive operations
also have codomain `J`; degree zero has value one in the ambient ring. The factorial
quotient is taken in `ℕ`, then cast to `C`, so no integer is inverted in `C`.

Proof:
1. Apply lem-sfb-pd-check-generators (Stacks Tag 07GP), with its ring `A = C`, ideal
   `I = J`, generating set `S`, and operations `g = δ`. The degree-zero convention,
   identity, homogeneity and addition assumptions are precisely its global axioms;
   the two generator assumptions are its multiplication and iteration axioms.
   Thus these very operations form an ordinary divided-power structure on `J`.
   Neither finiteness nor nonemptiness of `S`, nor division in `C`, is required.
2. Unpack def-sfb-ordinary-divided-power-structure, namely Mathlib's `DividedPowers`,
   to obtain its multiplication and iteration identities on every element of `J`.
   These give the first two conjuncts, and the structure from step 1 gives the third.
   If `S` is empty, its spanning property forces `J = 0`; homogeneity at scalar zero
   forces all positive operations at zero to vanish, so this case is included.
-/
theorem generator_criterion {C : Type u} [CommRing C]
    (J : Ideal C) (S : Set J) (hS : Ideal.span (Subtype.val '' S) = J)
    (δ : ℕ → J → C)
    (hzero : ∀ z : J, δ 0 z = 1)
    (hmem : ∀ (n : ℕ), 0 < n → ∀ z : J, δ n z ∈ J)
    (hone : ∀ z : J, δ 1 z = (z : C))
    (hscalar : ∀ (n : ℕ), 0 < n → ∀ (c : C) (z : J),
      δ n (c • z) = c ^ n * δ n z)
    (hadd : ∀ (n : ℕ), 0 < n → ∀ z w : J,
      δ n (z + w) = ∑ i ∈ Finset.range (n + 1), δ i z * δ (n - i) w)
    (hmul : ∀ s ∈ S, ∀ (n m : ℕ), 0 < n → 0 < m →
      δ n s * δ m s = (Nat.choose (n + m) n : C) * δ (n + m) s)
    (hcomp : ∀ s ∈ S, ∀ (n m : ℕ), 0 < n → ∀ hm : 0 < m,
      δ n ⟨δ m s, hmem m hm s⟩ =
        (((n * m).factorial / (n.factorial * m.factorial ^ n) : ℕ) : C) * δ (n * m) s) :
    (∀ (z : J) (n m : ℕ), 0 < n → 0 < m →
      δ n z * δ m z = (Nat.choose (n + m) n : C) * δ (n + m) z) ∧
    (∀ (z : J) (n m : ℕ), 0 < n → ∀ hm : 0 < m,
      δ n ⟨δ m z, hmem m hm z⟩ =
        (((n * m).factorial / (n.factorial * m.factorial ^ n) : ℕ) : C) * δ (n * m) z) ∧
    ∃ γ : DividedPowers J, ∀ (n : ℕ) (z : J), γ.dpow n z = δ n z := by
  sorry

end DividedPowers
