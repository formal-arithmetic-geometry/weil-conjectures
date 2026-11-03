/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralTensorPullback.IntegralTensorPullbackData
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal

import WeilConjectures.AlgebraicGeometry.IntegralTensorPullback.IntegralConstantCyclicQuotient
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import WeilConjectures.CategoryTheory.SixFunctors.LaxTensorCyclicCokernel

/-! # Tensor reduction under restriction to constant integral coefficients

Source: the finite reduction part of `det-lem-int-tensor-pullback.proof.md`.
(blueprint: lem-sfb-finite-scalar-tensor-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralTensorPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.IntegralTensorPullback

namespace AlgebraicGeometry.ProEtale.IntegralTensorPullback

/-- The canonical lax tensor comparison is invertible when its second argument
is a positive finite quotient of the continuous integral coefficient.

Source: blueprint `det-lem-int-tensor-pullback.proof.md`, finite reduction comparison.
(blueprint: lem-sfb-finite-scalar-tensor-iso).

Proof: the quotient at exponent n+1 is the cokernel of the same uniformizer power
on the continuous unit and on the constant unit. For the latter, sheafify the
ordinary quotient sequence of the discrete integers; continuous functions to the
finite discrete quotient are locally constant, so the canonical constant-function
map identifies its cokernel with the restricted continuous quotient, with the same
quotient unit. The continuous assertion is the uniformizer resolution. Tensor both
cokernel diagrams with M and Res(M), respectively. Tensor preserves cokernels and
restriction is exact. Both resulting diagrams are cokernels of multiplication by
the same uniformizer power on Res(M). The canonical comapTensorHom sends m tensor 1
to m tensor 1, so it is the comparison between these two cokernels and is invertible.
Inverse image preserves these cokernel diagrams and their tensor structures, giving
the assertion on X. Zero modules, empty schemes and the first positive exponent
satisfy the same cokernel argument. -/
theorem finite_scalar_tensor_isIso (X : Scheme.{u}) (n : ℕ)
    (M : AdicCompletion.Modules l E X) :
    IsIso (Mod.comapTensorHom ((upperStarFromPoint X).map (constantToIntegral l E))
      M (AdicCompletion.finiteModule l E X n)) := by
  obtain ⟨dR, dC, ⟨zR, ⟨hR⟩⟩, ⟨zC, ⟨hC⟩⟩, hs⟩ :=
    integral_constant_cyclic_quotient l E X n
  let := Mod.comapLaxMonoidal ((upperStarFromPoint X).map (constantToIntegral l E))
  exact laxTensorCyclicCokernel (restriction l E X)
    (AdicCompletion.finiteModule l E X n) (AdicCompletion.finiteUnit l E X n)
    dR dC zR hR zC hC hs M

end AlgebraicGeometry.ProEtale.IntegralTensorPullback
