/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Sheaf.RingTheory.FormallySmoothAdic
import Sheaf.RingTheory.FormallySmoothAdicLiftIntoComplete

/-!
# Extending derivations along formally smooth adic maps

Source: Stacks Project, More on Algebra, Lemma 15.50.1 (Tag 07PL), using
Lemma 15.38.5 (Tag 07NJ), in the generality of its dual-number proof
(blueprint: lem-weil-pbc-fs-adic-lift-derivation).
-/

@[expose] public section

universe u v

namespace Derivation

/-- An absolute derivation of `R` extends to an absolute derivation of an `R`-algebra `S`
that is `n`-adically complete and formally smooth for the `n`-adic topology.
Absolute derivations are represented by `Derivation ℤ`: additivity implies ℤ-linearity,
and the Leibniz identity implies vanishing at one.
Source: Stacks Project, More on Algebra, Lemma 15.50.1 (Tag 07PL), using Tag 07NJ.
(blueprint: lem-weil-pbc-fs-adic-lift-derivation)

Proof (the node's six steps, without locality or Noetherian hypotheses):
1. Form the dual numbers `A = S[ε] = S[X]/(X²)` using def-weil-polynomial-ring and
   def-weil-pbc-algebra-hom-quotient. Division by the monic polynomial `X²` gives unique
   expressions `a + ε b`. Multiplication is `(a + ε b)(c + ε d) = ac + ε(ad + bc)`.
   The ideal `J = ε S` has square zero; the projection `q(a + ε b) = a` has kernel `J`
   and identifies `A/J` with `S`.
2. Give `A` its `R`-algebra structure through `ψ(r) = φ(r) + ε φ(D(r))`, where
   `φ = algebraMap R S`. Additivity and the Leibniz rule make `ψ` a ring map:
   `D(1) = 0`, and the ε-coefficient of `ψ(a)ψ(b)` is `φ(D(ab))`. Since `qψ = φ`,
   the identity of `S = A/J` is an `R`-algebra map (def-weil-pbc-algebra-hom-quotient).
3. Put `I = n A`. Its powers consist of `a + ε b` with `a,b ∈ n^m`.
   Thus `A/I^m` is additively the product of two copies of `S/n^m`, compatibly with
   transition maps. The canonical completion map of `A` is the product of two copies
   of that of `S`, hence bijective by def-weil-pbc-adically-complete-ring.
4. We have `J² = 0 ⊆ I`. Also `J + I^m` consists of pairs with first coordinate in
   `n^m`; separatedness of `S` gives `⋂ n^m = 0`, hence `⋂ (J + I^m) = J`.
   Finally the identity of `S = A/J` maps `n` into `q(I) = n`.
5. Apply lem-weil-pbc-fs-adic-lift-into-complete (Tag 07NJ), using
   def-weil-pbc-formally-smooth-adic and the completeness and closedness just checked.
   It gives an `R`-algebra map `σ : S → A` with `qσ = id`. The discrete lifting
   condition alone does not directly apply to this identity map unless `n` is nilpotent.
6. Write `σ(s) = s + ε D'(s)`. Additivity and multiplicativity of `σ` show that `D'`
   is additive and satisfies the Leibniz rule. The equality `σφ = ψ` gives
   `D'(φ(r)) = φ(D(r))` by comparing ε-coefficients. -/
theorem exists_extension_of_formallySmoothAdic
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (n : Ideal S) [IsAdicComplete n S] (h : Algebra.FormallySmoothAdic R S n)
    (D : Derivation ℤ R R) :
    ∃ D' : Derivation ℤ S S, ∀ r : R, D' (algebraMap R S r) = algebraMap R S (D r) := by
  sorry

end Derivation
