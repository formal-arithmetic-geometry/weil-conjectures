/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q126
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Sheaf.RingTheory.ProjectiveOverLocalFree

/-!
# Injective projective-module maps over a nil local ring are pure

Source: Stacks Project, More on Algebra, Tags 05GM, 05GN, 05GP, and 05GQ,
implication (1) to (2), specialized to a local ring with nil maximal ideal
(blueprint: lem-trf-nil-local-projective-injection-pure).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v w t

open scoped TensorProduct

namespace LinearMap

/--
Let `A` be a commutative local ring whose maximal ideal consists of nilpotent elements.
An injective map `u` between arbitrary projective `A`-modules remains injective after
left tensoring with every `A`-module; in particular, it remains injective after right
tensoring with the residue field. This is the specialization of Stacks Project,
More on Algebra, Tags 05GM, 05GN, 05GP, and 05GQ.
(blueprint: lem-trf-nil-local-projective-injection-pure).

Proof plan: projective modules over a local ring are free by
`Module.free_of_projective_of_isLocalRing`. For a finite free source and free target,
induct on the source rank: a coefficient of the first basis vector is a unit, split
off that coordinate, and apply the induction hypothesis to the complementary kernel.
The nilpotence hypothesis supplies a common nonzero annihilator for finitely many
maximal-ideal coefficients. Every tensor element has finite basis support, so the
finite-source retraction proves injectivity after tensoring with an arbitrary module.
The residue-field clause follows by taking the residue field and swapping tensor factors.
-/
theorem injective_lTensor_of_projective_of_nil_maximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A]
    (hnil : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → IsNilpotent a)
    (P : Type v) (Q : Type w) [AddCommGroup P] [AddCommGroup Q]
    [Module A P] [Module A Q] [Module.Projective A P] [Module.Projective A Q]
    (u : P →ₗ[A] Q) (hu : Function.Injective u) :
    (∀ (T : Type t) [AddCommGroup T] [Module A T],
      Function.Injective (u.lTensor T)) ∧
      Function.Injective (u.rTensor (A ⧸ IsLocalRing.maximalIdeal A)) := by
  sorry

end LinearMap

end
