/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Finite modules over adically complete rings

Source: Stacks Project, Algebra, Lemma 10.96.12 (Tag 031D), including the
lifting-of-generators assertion in its proof
(blueprint: lem-weil-pbc-finite-over-complete-ring).
-/

universe u v

namespace Module

/-- (blueprint: lem-weil-pbc-finite-over-complete-ring)
Stacks Project, Algebra, Lemma 10.96.12 (Tag 031D): a Hausdorff module over an
`I`-adically complete ring is finite if its reduction modulo `I` is finite.
Every finite family whose images generate the reduction already generates the module.

Proof (the node's successive-approximation form of the proof of Tags 031D and 0315):
1. Let `x₁, …, xᵣ` lift generators of `M/IM`, and let `N` be their span. For each `k`,
   express any element of `I^k M` modulo `I^(k+1) M` as a combination of the `xᵢ`
   with coefficients in `I^k`: expand it as a finite sum of products, then express
   each module factor modulo `IM` using the given quotient generators.
2. For `m : M`, repeatedly apply step 1 to obtain errors `mₙ ∈ I^n M` and coefficient
   partial sums `sᵢ⁽ⁿ⁾` with `m = ∑ᵢ sᵢ⁽ⁿ⁾ xᵢ + mₙ`. The differences of successive
   coefficients lie in `I^n`, so these partial sums give compatible residue classes.
3. By completeness of `A` [def-weil-pbc-adically-complete-ring], the compatible classes
   in the completion [def-weil-pbc-adic-completion] lift to coefficients `aᵢ : A`.
   For all `n`, `aᵢ - sᵢ⁽ⁿ⁾ ∈ I^n`.
4. Thus `m - ∑ᵢ aᵢ xᵢ` lies in every `I^n M`, hence vanishes by Hausdorffness.
   The chosen family spans `M`. Finiteness of the quotient supplies such a finite family,
   giving `Module.Finite A M` [def-weil-finitely-generated-module]. -/
theorem finite_and_span_eq_top_of_adicComplete
    {A : Type u} [CommRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M]
    [IsAdicComplete I A] [IsHausdorff I M]
    [Module.Finite (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M))] :
    Module.Finite A M ∧
      ∀ (r : ℕ) (x : Fin r → M),
        Submodule.span (A ⧸ I)
          (Set.range (fun j ↦ (I • (⊤ : Submodule A M)).mkQ (x j))) = ⊤ →
        Submodule.span A (Set.range x) = ⊤ := by
  sorry

end Module
