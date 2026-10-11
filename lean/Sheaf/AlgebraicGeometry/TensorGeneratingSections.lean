/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.PositiveTensorFamily
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-!
# Tensor products of generating sections

Source: literature/stacks-project/modules.tex, Modules, Lemma 01AO
(blueprint: lem-sc-tensor-generating-sections).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The pure tensors of finite generating families generate the tensor product of
finitely many `𝒪_X`-modules. The parameter `n` means `n + 1` factors `M 0, …, M n`;
the tensor product is the left-associated `positiveTensorFamily` and the pure tensor of
one section from each factor is `positiveTensorFamilySection`
(def-sc-positive-tensor-family). The `i`-th factor carries the generating family
`s i 0, …, s i (m i)` in the sense of `SheafOfModules.GeneratingSections` (the free-module
map is an epimorphism); the conclusion is that the pure tensors indexed by all tuples
`(j_i)` with `0 ≤ j_i ≤ m i` generate the tensor product.

Proof:
1. By def-weil-pbc-generating-sections and lem-weil-pbc-locally-surjective-iff-stalks,
each epimorphic free-module map says that the germs of its sections generate every stalk.
2. Induct on the number of factors using lem-weil-pbc-module-stalk-tensor: the stalk of
an iterated tensor product is the iterated tensor product of the stalks, and the germ of
a pure tensor section corresponds to the pure tensor of the germs.
3. Pure tensors span a tensor product over a ring. Expanding each factor in its given
finite generators expresses every pure tensor as a linear combination of the displayed
pure tensors. Apply this successively to the factors.
4. Hence the tuple-indexed free-module map is surjective on each stalk. By
lem-weil-pbc-locally-surjective-iff-stalks it is surjective as a sheaf map, exactly
that these sections generate, by def-weil-pbc-generating-sections.

Source: literature/stacks-project/modules.tex, Lemma 01AO (proof omitted there;
iterated finite-family form), Sheaves Lemma 0H7H, and Modules Lemma 01CB
(blueprint: lem-sc-tensor-generating-sections). -/
theorem tensor_generating_sections {X : Scheme.{u}}
    (n : ℕ) (M : Fin (n + 1) → X.Modules) (m : Fin (n + 1) → ℕ)
    (s : ∀ i, ULift.{u} (Fin (m i + 1)) → (M i).sections)
    (hs : ∀ i, Epi ((M i).freeHomEquiv.symm (s i))) :
    Epi ((positiveTensorFamily n M).freeHomEquiv.symm
      (fun j : (∀ i, ULift.{u} (Fin (m i + 1))) ↦
        positiveTensorFamilySection n M (fun i ↦ s i (j i)))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
