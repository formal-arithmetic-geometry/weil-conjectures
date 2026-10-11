/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Ideal.Defs

/-!
# Kernels, images, and cokernels of finitely presented modules over a coherent ring

Source: Stacks Project, Algebra, Lemmas 05CW and 05CX
(blueprint: lem-sc-coherent-ring-fp-kernel-cokernel).
-/

universe u v w

namespace Module

/-- Over a commutative ring whose finitely generated ideals are finitely presented, kernels,
images, and cokernels of maps between finitely presented modules are finitely presented.
Source: Stacks Project, Algebra, Definition 05CU and Lemmas 05CW, 05CX
(blueprint: lem-sc-coherent-ring-fp-kernel-cokernel).

Proof:
1. The ideal hypothesis makes `R` coherent as a module over itself (Definition 05CU).
   Lemma 05CW(4), by induction, makes every finite free module coherent. A finitely
   presented module is a cokernel of a map between finite free modules, hence coherent
   by 05CW(3), as in 05CX. Thus `M` and `N` are coherent. Lemma 05CW(2) makes the kernel
   of `f` finitely generated; as a finitely generated submodule of coherent `M`, it is
   finitely presented by Definition 05CU.
2. Images under `f` of finite generators of `M` generate its image. This finitely
   generated submodule of coherent `N` is finitely presented by Definition 05CU.
3. The cokernel is `N` modulo the image. Choose a finite presentation of `N` and lift
   finite generators of the image to its finite free presenting module. Append the
   lifts to the relation generators of `N`; these give a finite presentation of the
   quotient, hence of the cokernel. -/
theorem finitePresentation_ker_range_cokernel_of_fg_ideals
    {R : Type u} [CommRing R]
    (hR : ∀ (I : Ideal R), I.FG → Module.FinitePresentation R I)
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    (f : M →ₗ[R] N) :
    Module.FinitePresentation R (LinearMap.ker f) ∧
      Module.FinitePresentation R (LinearMap.range f) ∧
      Module.FinitePresentation R (N ⧸ LinearMap.range f) := by
  sorry

end Module
