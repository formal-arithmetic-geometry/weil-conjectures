/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Continuous completion of a module-valued derivation

Source: Stacks Project, More on Algebra, Tag 07PE, proof of (1), in its module-valued form;
Algebra, Tag 05GG, for the kernels of the completion projections
(blueprint: lem-trf-module-valued-derivation-completion).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Derivation

/-- A derivation into an arbitrary module extends uniquely continuously to the completions.
The quotient derivations use the action pulled back along `A/I^(r+1) → A/I^r`.
All base-ring module structures are the canonical restrictions of scalars, supplied explicitly
by `Module.compHom`; no separate action on `M` is assumed. Mathlib indexes completions by
all natural numbers; the zeroth quotient is zero, so the positive coordinates give the same
inverse limit. The two coordinate clauses express the shifted projection formula and its
version using a lift modulo the extended ideal power, respectively.

Source: Stacks Project, More on Algebra, Tag 07PE, proof of (1), module-valued version;
Algebra, Tag 05GG (blueprint: lem-trf-module-valued-derivation-completion).

Proof:
1. Repeated Leibniz expresses the differential of a product of `r+1` ideal factors, with
   an arbitrary coefficient, as a sum with at least `r` ideal factors in every term.
   Additivity gives `d(I^(r+1)) ⊆ I^r M`.
2. Therefore reducing `d(a)` modulo `I^r M` descends to `A/I^(r+1)`. Reducing the
   derivation identities gives exactly the indicated quotient derivation.
3. Representing the `(r+2)`-coordinate by an element of `A` proves compatibility after
   reduction. The shifted coordinates consequently define an element of the module
   completion. Addition, vanishing on the base ring, and Leibniz hold coordinatewise for
   Mathlib's componentwise completion action. On the image of `A` the map is `j ∘ d`.
4. Apply the module completion theorem (lem-weil-pbc-module-completion-complete,
   Mathlib's `AdicCompletion.pow_smul_top_eq_ker_eval` and `isAdicComplete`) to both `A`
   and `M`. Finite generation of `I` identifies projection kernels with ideal powers,
   makes projections surjective, and gives separatedness. Also `(IC)^t = I^t C`.
   Thus a representative of coordinate `r+1` is exactly a lift modulo `(IC)^(r+1)`.
5. An element of `(IC)^(r+1)` has zero `(r+1)`-coordinate, hence its differential has
   zero `r`-coordinate and lies in `I^r N`. This proves the bound and continuity.
6. For another continuous extension and a fixed positive `r`, choose its continuity
   exponent `s₀`. Lift an element modulo exponent `max s₀ (r+1)` to `A`. Both
   derivations then agree modulo `I^r N` with the differential of this lift. They agree
   modulo every positive power; separatedness of `N` gives equality and uniqueness.
-/
theorem exists_unique_continuous_module_completion
    {k : Type u} {A : Type v} [CommRing k] [CommRing A] [Algebra k A]
    (I : Ideal A) (hI : I.FG) (M : Type w) [AddCommGroup M] [Module A M]
    (d : @Derivation k A M _ _ _ _ _ (Module.compHom M (algebraMap k A))) :
    ∃ dQ : ∀ (r : ℕ), 1 ≤ r →
        @Derivation k (A ⧸ I ^ (r + 1))
          (M ⧸ (I ^ r • ⊤ : Submodule A M)) _ _ _ _
          (Module.compHom (M ⧸ (I ^ r • ⊤ : Submodule A M))
            (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ r))))
          (Module.compHom (M ⧸ (I ^ r • ⊤ : Submodule A M)) (algebraMap k A)),
      (∀ (r : ℕ) (hr : 1 ≤ r) (a : A),
        dQ r hr (Ideal.Quotient.mk (I ^ (r + 1)) a) =
          (I ^ r • ⊤ : Submodule A M).mkQ (d a)) ∧
      (∀ (r : ℕ) (hr : 1 ≤ r) (x : AdicCompletion I A),
        AdicCompletion.transitionMap I M (Nat.le_succ r)
            (dQ (r + 1) (Nat.succ_pos r) (AdicCompletion.evalₐ I (r + 2) x)) =
          dQ r hr (AdicCompletion.evalₐ I (r + 1) x)) ∧
      ∃ D : @Derivation k (AdicCompletion I A) (AdicCompletion I M) _ _ _ _ _
          (Module.compHom (AdicCompletion I M) (algebraMap k (AdicCompletion I A))),
        (∀ a : A, D (algebraMap A (AdicCompletion I A) a) =
          AdicCompletion.of I M (d a)) ∧
        (∀ (r : ℕ), 1 ≤ r → ∃ s : ℕ, 1 ≤ s ∧
          ∀ x : AdicCompletion I A,
            x ∈ (I.map (algebraMap A (AdicCompletion I A))) ^ s →
            D x ∈ I ^ r • (⊤ : Submodule A (AdicCompletion I M))) ∧
        (∀ E : @Derivation k (AdicCompletion I A) (AdicCompletion I M) _ _ _ _ _
            (Module.compHom (AdicCompletion I M) (algebraMap k (AdicCompletion I A))),
          (∀ a : A, E (algebraMap A (AdicCompletion I A) a) =
            AdicCompletion.of I M (d a)) →
          (∀ (r : ℕ), 1 ≤ r → ∃ s : ℕ, 1 ≤ s ∧
            ∀ x : AdicCompletion I A,
              x ∈ (I.map (algebraMap A (AdicCompletion I A))) ^ s →
              E x ∈ I ^ r • (⊤ : Submodule A (AdicCompletion I M))) → E = D) ∧
        (∀ (r : ℕ) (hr : 1 ≤ r) (x : AdicCompletion I A),
          AdicCompletion.eval I M r (D x) =
            dQ r hr (AdicCompletion.evalₐ I (r + 1) x)) ∧
        (∀ (r : ℕ), 1 ≤ r → ∀ (x : AdicCompletion I A) (a : A),
          x - algebraMap A (AdicCompletion I A) a ∈
              (I.map (algebraMap A (AdicCompletion I A))) ^ (r + 1) →
            AdicCompletion.eval I M r (D x) =
              (I ^ r • ⊤ : Submodule A M).mkQ (d a)) ∧
        (∀ (r : ℕ), 1 ≤ r → ∀ x : AdicCompletion I A,
          x ∈ (I.map (algebraMap A (AdicCompletion I A))) ^ (r + 1) →
            D x ∈ I ^ r • (⊤ : Submodule A (AdicCompletion I M))) := by
  sorry

end Derivation
