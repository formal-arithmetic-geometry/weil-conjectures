/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Descent of a basis along an affine groupoid

Source: Stacks Project, Tag 03C8, finite nonempty index-set case
(blueprint: lem-a1-affine-groupoid-basis-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A basis consisting of target images descends to the invariant ring, and the canonical
comparison from the tensor square over that ring is a ring isomorphism.
Source: Stacks Project, Tag 03C8 (blueprint: lem-a1-affine-groupoid-basis-descent).
The invariant ring is `RingHom.eqLocus`; `Spec.preimage` is the inverse of `Spec.map`.
The last formula specifies the comparison uniquely on pure tensors.

Proof plan (the six steps of the DAG node):
1. Put epsilon = e-sharp. The identity laws and contravariant functoriality of Spec
   (def-weil-affine-spectrum) give epsilon sigma = epsilon tau = id. The equalizer C is
   a unital subring, and sigma and tau agree on it.
2. Identify the coordinate ring of the pullback with D = B tensor_(sigma,A,tau) B
   (lem-weil-pbc-fibre-product-affine-spectra, def-weil-pbc-module-tensor-product).
   For p0(b) = b tensor 1, p1(b) = 1 tensor b and Delta = c-sharp, balancing and the
   composition source/target laws give p0 sigma = p1 tau, Delta sigma = p1 sigma,
   and Delta tau = p0 tau.
3. Base change the given basis along tau into the second B. The vectors
   y_j = p0(tau(x_j)) are a basis over that second B, acting through p1
   (lem-weil-pbc-free-module-base-change-free, def-weil-pbc-free-module).
4. Expand tau(a) = sum sigma(a_j) tau(x_j). Applying Delta and applying p0 give
   two expansions of p0(tau(a)) in the y_j basis, with coefficients sigma(a_j) and
   tau(a_j). Uniqueness gives sigma(a_j) = tau(a_j), so all a_j belong to C
   (def-weil-pbc-free-module).
5. Apply epsilon to obtain a = sum a_j x_j, proving C-spanning. Applying tau to a
   C-linear relation among the x_j gives an A-linear relation among the tau(x_j),
   so all coefficients vanish. Thus the specified x_j form a C-basis of A
   (def-weil-pbc-free-module).
6. The tensor-product ring universal property constructs phi(a tensor b) = sigma(a) tau(b)
   (lem-weil-pbc-algebra-tensor-pushout-universal-property). Base change of the descended
   basis gives the A-basis 1 tensor x_j of the source; phi sends it to the assumed
   A-basis tau(x_j) of the target. Surjectivity follows by expanding any target element;
   zero kernel follows from uniqueness of coefficients. Hence phi is a ring isomorphism
   (lem-weil-pbc-free-module-base-change-free, def-weil-pbc-free-module). -/
theorem affineGroupoid_basis_descent (A B : CommRingCat.{u})
    (s t : Spec B ⟶ Spec A) (e : Spec A ⟶ Spec B) (i : Spec B ⟶ Spec B)
    (c : pullback s t ⟶ Spec B) (_hG : IsGroupoidScheme s t e i c)
    (r : ℕ) (_hr : 1 ≤ r) (x : Fin r → A)
    (_hbasis : ∀ b : B, ∃! a : Fin r → A,
      b = ∑ j : Fin r, (Spec.preimage s).hom (a j) * (Spec.preimage t).hom (x j)) :
    (∃ b : Module.Basis (Fin r)
        (RingHom.eqLocus (Spec.preimage s).hom (Spec.preimage t).hom) A,
      ∀ j : Fin r, b j = x j) ∧
    ∃ f : (A ⊗[RingHom.eqLocus (Spec.preimage s).hom (Spec.preimage t).hom] A) ≃+* B,
      ∀ a a₂ : A, f (a ⊗ₜ a₂) = (Spec.preimage s).hom a * (Spec.preimage t).hom a₂ := by
  sorry

end AlgebraicGeometry
