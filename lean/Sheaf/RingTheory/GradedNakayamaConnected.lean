/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q125
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Graded Nakayama for connected graded algebras

Source: Stacks Project, Algebra, Tag 0EKB, `lemma-graded-NAK`, parts (4) and (1),
and `section-graded` (blueprint: lem-sfb-graded-nakayama-connected).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace GradedAlgebra

/-- Homogeneous lifts of generators modulo the positive ideal generate a finite graded module;
a finite graded module equal to its positive-ideal multiple is zero.

Source: Stacks Project, Algebra, Tag 0EKB, `lemma-graded-NAK`, parts (4) and (1),
specialized to a connected graded algebra; `section-graded` fixes the grading conventions
(blueprint: lem-sfb-graded-nakayama-connected).

Proof, following the node's five steps:
1. The positive components form an ideal since multiplying by a nonnegative-degree component
preserves positive degree. Finite generation (`def-weil-finitely-generated-module`) gives a
finite generating family. Replacing each generator by its finitely many homogeneous components
gives homogeneous generators; an empty generating family already means the module is zero.
2. If `IM = M`, choose a generator of minimum degree. Express it as a linear combination of
the homogeneous generators with coefficients in `I`. Each positive homogeneous coefficient
times any generator has strictly larger degree. Projection to the minimum degree therefore
shows that the chosen generator is zero.
3. Remove that generator and induct on the number of generators, with the empty family as
base case. This proves the second clause.
4. For the first clause, the submodule `Q` spanned by the proposed homogeneous lifts is graded:
decomposing the coefficients shows that every homogeneous component remains in `Q`.
Thus `M/Q` inherits an internal integer grading compatible with the algebra grading and is
finite as a quotient of a finite module.
5. Spanning modulo `IM` gives `M = Q + IM`. Its image in `M/Q` says `I(M/Q) = M/Q`.
Apply the second clause, already proved in steps 1--3, to conclude `M/Q = 0`, so `Q = M`.
The proof permits negative module degrees, the zero module and an empty family, and uses
neither Noetherianity nor finite type of the algebra. -/
theorem nakayama_connected {k : Type u} [Field k]
    {A : Type v} [CommRing A] [Algebra k A]
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
    (hzero : 𝒜 0 = LinearMap.range (Algebra.linearMap k A))
    {M : Type w} [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] [Module.Finite A M]
    (ℳ : ℤ → AddSubgroup M) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (a : ℕ) (b : ℤ) (f : A) (m : M),
      f ∈ 𝒜 a → m ∈ ℳ b → f • m ∈ ℳ ((a : ℤ) + b)) :
    (∀ (r : ℕ) (x : Fin r → M),
      (∀ i : Fin r, SetLike.IsHomogeneousElem ℳ (x i)) →
      Submodule.span k (Set.range (fun i : Fin r ↦
        ((HomogeneousIdeal.irrelevant 𝒜).toIdeal • (⊤ : Submodule A M)).mkQ (x i))) = ⊤ →
      Submodule.span A (Set.range x) = ⊤) ∧
    ((HomogeneousIdeal.irrelevant 𝒜).toIdeal • (⊤ : Submodule A M) = ⊤ →
      Subsingleton M) := by
  sorry

end GradedAlgebra
