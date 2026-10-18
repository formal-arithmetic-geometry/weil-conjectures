/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# A freeness criterion for countably generated modules

Source: Stacks Project, Algebra, Tag 0591, `lemma-freeness-criteria`
(blueprint: lem-trf-countably-generated-freeness-criterion).
-/

@[expose] public section

universe u v

namespace Module

/-- A countably generated module is free if each element of every complement of a finite
free summand belongs to a free direct summand of that complement.

Source: Stacks Project, Algebra, Tag 0591, `lemma-freeness-criteria`
(blueprint: lem-trf-countably-generated-freeness-criterion).

Proof:
1. Enumerate the countable generating subset as a sequence, repeating elements or inserting
   zero when the subset is finite or empty. Each element is a finite linear combination of
   terms of this sequence.
2. Inductively construct finite free summands `F₁, ..., Fₙ` whose sum `Sₙ` is a direct summand
   of `M` containing the first `n` generators. The union of their finite bases is a finite
   basis of `Sₙ` (def-weil-pbc-free-module). Split `M` as `N ⊕ Sₙ` and project the next
   generator to `N`. The hypothesis puts this component in a free direct summand `G` of `N`.
3. Choose a basis of `G`. Only finitely many basis vectors occur in this component, so their
   span is finite free and has the span of the remaining basis vectors as a complement in
   `G` (def-weil-pbc-free-module). Use it as `Fₙ₊₁`; composing the splittings gives `Sₙ₊₁`
   as a direct summand containing the first `n + 1` generators.
4. Every element of `M` lies in some `Sₙ`, since it involves only finitely many generators.
   Each finite relation lies in one finite-stage direct sum, so its components vanish.
   Thus `M` is the direct sum of the `Fᵢ`.
5. The disjoint union of their finite bases is a basis of that direct sum: finite support
   gives spanning, and coordinatewise uniqueness gives independence
   (def-weil-pbc-free-module). Hence `M` is free. -/
theorem free_of_countable_generators_of_free_summands
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (hcountable : ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤)
    (hsummands : ∀ (N F : Submodule R M), IsCompl N F →
      (∃ n : ℕ, Nonempty (Module.Basis (Fin n) R F)) →
      ∀ x : N, ∃ G H : Submodule R N, IsCompl G H ∧ x ∈ G ∧ Module.Free R G) :
    Module.Free R M := by
  sorry

end Module
