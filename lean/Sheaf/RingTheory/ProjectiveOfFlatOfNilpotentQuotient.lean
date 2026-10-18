/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Torsion.Basic
import Sheaf.RingTheory.NilpotentProjectiveModuleLift
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Projectivity of a flat module lifts across a nilpotent ideal

Source: Stacks Project, Algebra, Tag 05CG, `lemma-lift-projective`
(blueprint: lem-trf-local-nilpotent-projective-flat-lift).
-/

@[expose] public section

universe u v

open scoped Pointwise

namespace Module

/-- A flat module whose reduction modulo a nilpotent ideal is projective is projective.
No finite generation assumption is needed. Source: Stacks Project, Algebra, Tag 05CG,
`lemma-lift-projective` (blueprint: lem-trf-local-nilpotent-projective-flat-lift).

Proof plan:
1. Choose `N ≥ 1` with `I ^ N = 0`. By
   `lem-weil-pbc-nilpotent-projective-module-lift`, lift the projective module `M/IM`
   to a projective `A`-module `P` with an `A/I`-linear isomorphism `α : P/IP ≃ M/IM`.
   The lifting property in `def-weil-pbc-projective-module` lifts the composite
   `P → P/IP → M/IM` along `M → M/IM` to an `A`-linear map `f : P → M` reducing to `α`.
   By `lem-weil-pbc-projective-module-flat`, `P` is flat, as is `M` by hypothesis.
2. For `X = P` or `M` and `0 ≤ a < N`, tensor `I^a ↪ A` with `X`.
   By `lem-weil-pbc-flat-tensor-exact`, multiplication identifies `I^a ⊗ X` with `I^a X`;
   the same applies to `a+1`. Tensoring `I^(a+1) → I^a → I^a/I^(a+1) → 0` by
   `lem-weil-pbc-tensor-right-exact` and taking its cokernel therefore identifies
   `(I^a/I^(a+1)) ⊗[A] X` with `I^a X/I^(a+1) X`, by `r ⊗ x ↦ r x`.
3. The ideal `I` annihilates `Q = I^a/I^(a+1)`. Clause (2) of
   `lem-weil-pbc-tensor-over-quotient-ring` identifies `Q ⊗[A] X` with
   `Q ⊗[A/I] (X/IX)`. Under these multiplication maps, the graded map induced by `f`
   is exactly `1 ⊗ α`, since `f(r x) = r f(x)`. It is invertible with inverse
   `1 ⊗ α⁻¹`, as checked on generating pure tensors. Every graded map is thus bijective.
4. Descending induction shows `I^a P → I^a M` is bijective, starting at `a = N`,
   where both modules vanish. At the induction step, graded injectivity sends an element
   of the kernel into `I^(a+1) P`, where induction kills it. For surjectivity, first lift
   an element modulo `I^(a+1) M` using graded surjectivity, then lift the difference
   using the induction hypothesis. At `a = 0`, this proves `f` bijective. Its inverse
   is linear because uniqueness of preimages preserves addition and scalar multiplication.
5. Apply clause (2) of `lem-weil-pbc-projective-direct-summand` to `M ≃ P`:
   a module isomorphic to the projective module `P` is projective. -/
theorem projective_of_flat_of_nilpotent_quotient
    (A : Type u) [CommRing A] (I : Ideal A) (hI : IsNilpotent I)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Flat A M]
    [Module.Projective (A ⧸ I) (M ⧸ (I • (⊤ : Submodule A M)))] :
    Module.Projective A M := by
  sorry

end Module
