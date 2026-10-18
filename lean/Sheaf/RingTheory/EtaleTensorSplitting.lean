/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Ideal.IdempotentFG

/-!
# Tensor decomposition over an étale localization

Source: Stacks Project, Tag 0812, proof of `lemma-trick-fitting-ideal`, using
Tags 00U7, 00U8 and 00EH (blueprint: lem-trf-etale-tensor-splitting).
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace Algebra

/-- The tensor algebra over an étale localization splits with multiplication as its
first projection. The algebra structure on the tensor product is through the second factor.

Source: Stacks Project, Tag 0812, proof of `lemma-trick-fitting-ideal`
(blueprint: lem-trf-etale-tensor-splitting).

Proof plan:
1. The tensor pushout universal property gives the multiplication map `mu`, induced by
   localization on `C` and the identity on `B = C_h`. Its composite with the second-factor
   inclusion is the identity, so it is surjective
   (`lem-weil-pbc-algebra-tensor-pushout-universal-property`).
2. Base change the étale map `A → B` to `C → C tensor_A B`
   (`lem-weil-pbc-etale-ring-base-change`). The localization `C → B` is an open immersion
   (`lem-weil-pbc-principal-localization-open-immersion`), hence étale. Cancellation of
   étale morphisms shows that `mu` is étale
   (`lem-weil-pbc-etale-composition-cancellation`).
3. Its kernel is a finitely generated idempotent ideal
   (`lem-weil-pbc-surjective-etale-kernel-idempotent-fg`). Choose an idempotent `e`
   generating it (`lem-weil-pbc-fg-idempotent-ideal-idempotent-generator`). Put `q = 1-e`;
   then `eq = 0`, `q+e = 1`, `mu(e) = 0` and `mu(q) = 1`.
4. Give `D = eT` its corner-ring structure, with identity `e`, and its `B`-algebra
   structure `b ↦ e j(b)`. The map `t ↦ (mu(t), et)` is a `B`-algebra homomorphism.
5. Its inverse is `(b,d) ↦ q j(b)+d`. The identities above give one composite as the
   identity. For the other, `t-j(mu(t))` lies in `eT`, so `q j(mu(t)) = qt`, and
   `qt+et = t`. The first projection of the displayed map is exactly `mu`. -/
theorem exists_etaleLocalization_tensor_splitting
    (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
    [Module.Free A C] [Module.Finite A C] (h : C)
    [AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away h))))] :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra (Localization.Away h) D)
      (θ : @AlgEquiv (Localization.Away h) (C ⊗[A] Localization.Away h)
        (Localization.Away h × D) _ _ _
        (Algebra.TensorProduct.rightAlgebra (R := A) (A := C) (B := Localization.Away h)) _),
      ∀ t : C ⊗[A] Localization.Away h,
        (θ t).1 = Algebra.TensorProduct.productMap
          (IsScalarTower.toAlgHom A C (Localization.Away h))
          (AlgHom.id A (Localization.Away h)) t := by
  sorry

end Algebra
