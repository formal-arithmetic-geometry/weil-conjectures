/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Descent of extensions with direct-sum quotient

Source: Stacks Project, More on Algebra, proof of Lemma 05EG
(blueprint: lem-weil-pbc-direct-sum-extension-assembly).

Base change is written `S ⊗[R] M`, as in `LinearMap.baseChange`; tensor symmetry identifies
this with the source's `M ⊗[R] S`. Short exactness is expressed by injectivity, `Function.Exact`,
and surjectivity, the module interpretation of `CategoryTheory.ShortComplex.ShortExact`
via `ShortExact.moduleCat_exact_iff_function_exact` and its injective/surjective lemmas,
as in `LinearMap.exists_cyclic_extension_flat_descent`.
-/

universe u v w x y z

open TensorProduct DirectSum

namespace LinearMap

/-- Source: Stacks Project, More on Algebra, proof of Lemma 05EG, the reduction using
compatibility of Ext with arbitrary direct sums
(blueprint: lem-weil-pbc-direct-sum-extension-assembly).

If every extension with quotient a base-changed summand descends along a flat ring map,
then every extension with quotient the base-changed direct sum descends, fixing both ends.
The middle modules `T` range over one universe `z` in the hypothesis and the conclusion;
the pullbacks `T_j` of the proof are submodules of `T`, so they lie in that universe.

Proof: Pull back the given extension along each base-changed canonical inclusion, and use
its descent hypothesis to choose an R-extension of that summand. Surjectivity of the
Ext-one direct-sum comparison (lem-weil-pbc-ext-one-direct-sum) assembles these classes into
an R-extension of the direct sum. Base-changing extension equivalences preserves their
fixed endpoints, by identity and composition compatibility of def-weil-module-base-change.
Next use lem-weil-pbc-tensor-commutes-with-colimits to identify the base-changed direct sum
and its inclusions. The assembled sequence stays short exact by lem-weil-pbc-flat-tensor-exact
and lem-weil-pbc-tensor-right-exact. Pullbacks commute with flat base change: describe a
pullback as the kernel of the difference map out of a finite direct sum, use tensor's
compatibility with finite sums, and apply lem-weil-pbc-flat-tensor-exact to that kernel.
Consequently the assembled base-changed extension has the same pullback class on each
summand as the original extension. Injectivity of the Ext-one direct-sum comparison over S
(lem-weil-pbc-ext-one-direct-sum) gives an isomorphism of extensions fixing both ends. -/
theorem extension_descends_of_summands
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (_hflat : (algebraMap R S).Flat)
    {N : Type w} [AddCommGroup N] [Module R N]
    {J : Type x} (C : J → Type y) [∀ j, AddCommGroup (C j)] [∀ j, Module R (C j)]
    (_hC : ∀ (j : J) (T : Type z) [AddCommGroup T] [Module S T]
      (a : S ⊗[R] N →ₗ[S] T) (b : T →ₗ[S] S ⊗[R] C j),
      Function.Injective a → Function.Exact a b → Function.Surjective b →
      ∃ (E : Type (max w y)) (_ : AddCommGroup E) (_ : Module R E)
        (i : N →ₗ[R] E) (q : E →ₗ[R] C j),
        Function.Injective i ∧ Function.Exact i q ∧ Function.Surjective q ∧
        ∃ θ : S ⊗[R] E ≃ₗ[S] T,
          θ.toLinearMap.comp (i.baseChange S) = a ∧
          b.comp θ.toLinearMap = q.baseChange S)
    {T : Type z} [AddCommGroup T] [Module S T]
    (a : S ⊗[R] N →ₗ[S] T) (b : T →ₗ[S] S ⊗[R] (⨁ j, C j))
    (_ha : Function.Injective a) (_hab : Function.Exact a b)
    (_hb : Function.Surjective b) :
    ∃ (E : Type (max w x y)) (_ : AddCommGroup E) (_ : Module R E)
      (i : N →ₗ[R] E) (q : E →ₗ[R] (⨁ j, C j)),
      Function.Injective i ∧ Function.Exact i q ∧ Function.Surjective q ∧
      ∃ θ : S ⊗[R] E ≃ₗ[S] T,
        θ.toLinearMap.comp (i.baseChange S) = a ∧
        b.comp θ.toLinearMap = q.baseChange S := by
  sorry

end LinearMap
