/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Degreewise ordinary base tensor comparison

Source: Stacks Project, Tags 00CX, 05G3 and 08IB.
(blueprint: lem-pc-base-tensor-ordinary-degree-iso).
-/

@[expose] public section

set_option autoImplicit false

universe uR uA uB v

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

/-- Stacks Project, Tags 00CX and 05G3 (tensor universal property and base change),
and Tag 08IB (affine comparison).
(blueprint: lem-pc-base-tensor-ordinary-degree-iso).

Proof: define the forward B-linear map on generators by
b tensor m ↦ (1 tensor b) tensor m. Define the inverse on double pure tensors by
(a tensor b) tensor m ↦ b tensor (a m). R-balancing follows from the R-algebra
structures on A and B, and A-balancing follows from associativity of the A-action
on M. The first composite fixes b tensor m. The second fixes every double pure
tensor since (1 tensor b) tensor (a m) = (a tensor b) tensor m by A-balancing.
Tensor induction proves both composite identities. The resulting equivalence is
B-linear and has the claimed generator formula. No flatness is required.
Mathlib's Algebra.IsPushout.cancelBaseChange supplies this equivalence; its
symm_tmul lemma supplies the formula after identifying the scalar actions of
ModuleCat's ring-hom-based extension and restriction with the algebra actions. -/
theorem exists_baseTensorOrdinaryDegreeIso
    (R : Type uR) (A : Type uA) (B : Type uB)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (M : ModuleCat.{max uR uA uB v} A) :
    ∃ e :
      (extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).obj
        ((restrictScalars.{max uR uA uB v} (algebraMap R A)).obj M) ≅
      (restrictScalars.{max uR uA uB v}
        Algebra.TensorProduct.includeRight.toRingHom).obj
        ((extendScalars.{_, _, max uR uA uB v}
          (algebraMap A (A ⊗[R] B))).obj M),
      ∀ (b : B) (m : M), e.hom (b ⊗ₜ[R,algebraMap R B] m) =
        Algebra.TensorProduct.includeRight b ⊗ₜ[A,algebraMap A (A ⊗[R] B)] m := by sorry

end ModuleCat
