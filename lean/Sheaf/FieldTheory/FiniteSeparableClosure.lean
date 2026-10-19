/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.SeparableClosure
import Sheaf.FieldTheory.FiniteRelativeAlgebraicClosure
import Sheaf.FieldTheory.GeometricIrreducibilitySeparable

/-!
# Finite separable algebraic subextension of a finitely generated field extension

Source: Stacks Project, Algebra, Tag 037Q (lemma-make-geometrically-irreducible)
(blueprint: lem-zl-finite-separable-closure).
-/

@[expose] public section

universe u v

open CategoryTheory
open AlgebraicGeometry

/-- Let `K/k` be finitely generated, and let `k'` be the relative separable closure of `k` in
`K`. Then `K/k'` is geometrically irreducible and `k'/k` is finite.
Source: Stacks Project, Algebra, Tag 037Q (lemma-make-geometrically-irreducible)
(blueprint: lem-zl-finite-separable-closure).

Proof:
1. By the definition of the relative separable closure, `k'` is a subfield of `K` containing
   `k` and `k'/k` is separable algebraic. Let `F` be the separable algebraic closure of `k'`
   in `K`; it contains `k'` and `F/k'` is separable algebraic. Separable permanence
   (Fields, Tag 09HB) for the tower `k ⊆ k' ⊆ F` shows that `F/k` is separable algebraic, so
   every element of `F` lies in `k'` and `F = k'`: every element of `K` separably algebraic
   over `k'` lies in `k'`. The implication (2) ⇒ (1) of Tag 0G33, applied to `K/k'`, gives
   that `K/k'` is geometrically irreducible.
2. Let `k_alg` be the algebraic closure of `k` in `K`. Since `K/k` is finitely generated,
   `[k_alg : k] < ∞` by Fields, Tag 037J. Every element of `k'` is algebraic over `k`, so
   `k'` is an intermediate field of `k_alg/k`, and a subspace of a finite-dimensional
   `k`-vector space is finite-dimensional: `[k' : k] < ∞`.
-/
theorem finite_separable_closure
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) :
    GeometricallyIrreducible
        (Spec.map (CommRingCat.ofHom (algebraMap (separableClosure k K) K))) ∧
      FiniteDimensional k (separableClosure k K) := by
  constructor
  · apply (geometricallyIrreducible_iff_separableElements_mem
      (separableClosure k K) K).2
    intro α hα
    exact IntermediateField.mem_bot.mp
      ((separableClosure.separableClosure_eq_bot k K) ▸
        (mem_separableClosure_iff.mpr hα))
  · let := algebraicClosure.finite_of_fg k K hfg
    let f : separableClosure k K →ₐ[k] algebraicClosure k K :=
      IntermediateField.inclusion (le_algebraicClosure k K (separableClosure k K))
    exact FiniteDimensional.of_injective f.toLinearMap f.injective

end
