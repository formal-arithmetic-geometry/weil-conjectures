/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Sheaf.TraceFormula.ModuleDirectedColimitFP

/-!
# Universal injectivity detected on finitely presented tensor tests

Source: Stacks Project, Algebra, Tag 058K, `theorem-universally-exact-criteria`,
parts (1) and (2), and Tag 00FP for the Noetherian finite-module variant
(blueprint: lem-trf-universal-injective-finite-test).
-/

@[expose] public section

universe u v w t

namespace LinearMap

/-- Universal injectivity is detected by finitely presented tensor factors. Over a Noetherian
ring it is also detected by finite tensor factors. Here `f.lTensor Q` is the canonical map
`Q ⊗[R] M →ₗ[R] Q ⊗[R] N`, sending `q ⊗ m` to `q ⊗ f m`.
Source: Stacks Project, Algebra, Tag 058K, `theorem-universally-exact-criteria`, (1) and (2),
and Tag 00FP, `lemma-Noetherian-finite-type-is-finite-presentation`, (1)
(blueprint: lem-trf-universal-injective-finite-test).

Proof:
1. Universal injectivity implies injectivity for every finitely presented tensor factor by
   restriction of the quantifier.
2. Conversely, write an arbitrary test module Q as a small nonempty directed colimit of
   finitely presented modules Q_i by `lem-trf-module-directed-colimit-fp` (Tag 00HA).
   Each map `1_Q_i ⊗ f` is injective by the test hypothesis.
3. By `lem-weil-pbc-tensor-commutes-with-colimits` (Tag 00DD), tensoring this colimit with M
   and N gives colimit cocones whose legs are the canonical maps `a_i ⊗ 1`.
4. For an element x killed by `1_Q ⊗ f`, choose a representative x_i at some stage using
   `lem-weil-pbc-filtered-colimit-modules-elementwise` (Tags 00D6 and 00D7). Naturality of
   tensor maps, checked on pure tensors using `def-weil-pbc-module-tensor-product`, shows
   that `(1_Q_i ⊗ f)(x_i)` maps to zero in the target colimit. Eventual vanishing gives a
   later stage j where this image is zero. Naturality and injectivity at the finitely
   presented stage Q_j show that the transported x_i is zero, so x is zero.
5. Under the Noetherian hypothesis, every finite module is finitely presented by
   `lem-sc-noetherian-finite-module-finite-presentation` (Tag 00FP). Conversely the images
   of a finite free basis in any finite presentation generate the module, by
   `def-sc-finitely-presented-module` and `def-weil-finitely-generated-module`.
   Thus finite and finitely presented test modules coincide, giving the second equivalence.
-/
theorem universally_injective_tensor_iff
    {R : Type u} [CommRing R] {M : Type v} {N : Type w}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) :
    ((∀ (Q : Type (max u v w t)) [AddCommGroup Q] [Module R Q],
        Function.Injective (f.lTensor Q)) ↔
      ∀ (Q : Type (max u v w t)) [AddCommGroup Q] [Module R Q]
        [Module.FinitePresentation R Q], Function.Injective (f.lTensor Q)) ∧
    (IsNoetherianRing R →
      ((∀ (Q : Type (max u v w t)) [AddCommGroup Q] [Module R Q],
          Function.Injective (f.lTensor Q)) ↔
        ∀ (Q : Type (max u v w t)) [AddCommGroup Q] [Module R Q]
          [Module.Finite R Q], Function.Injective (f.lTensor Q))) := by
  sorry

end LinearMap
