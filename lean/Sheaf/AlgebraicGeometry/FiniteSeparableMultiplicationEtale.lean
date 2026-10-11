/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Multiplication of a finite separable field extension

Source: Stacks Project, Algebra, Lemma Tag 07QH, proof, second paragraph;
Lemma Tags 00U3, 00U2, 00U7 and Definition Tag 00U1
(blueprint: lem-weil-pbc-finite-separable-multiplication-etale).
-/

universe u v

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Multiplication of a finite separable field extension is etale.

Source: Stacks Project, Algebra, Lemma Tag 07QH, proof.
(blueprint: lem-weil-pbc-finite-separable-multiplication-etale).

Proof (the five steps of the node):
1. The finite separable extension `k'/k` is etale, by
   `lem-weil-pbc-finite-separable-extension-etale` (Stacks 00U3).
2. Base change makes the first inclusion `i₁ : k' → k' ⊗[k] k'` etale, by
   `lem-weil-pbc-etale-ring-base-change` (Stacks 00U2 (3)).
3. Multiplication satisfies `μ ∘ i₁ = id`, since `μ (a ⊗ 1) = a`. Contravariance of
   `Spec` (`def-weil-affine-spectrum`) gives `Spec μ ≫ Spec i₁ = id`.
4. This identity is an open immersion (`def-weil-open-immersion`), hence etale by
   `lem-weil-pbc-etale-composition-cancellation` (1). Since `Spec i₁` is etale,
   part (3) of that lemma gives that `Spec μ` is etale (Stacks 02GP, 02GW; ring
   version 00U7).
5. By `lem-weil-pbc-etale-ring-map-iff-etale-affine`, `μ` is an etale ring map:
   it is finitely presented, its first cotangent homology vanishes, and its
   Kahler differentials (`def-weil-pbc-kahler-differentials`) vanish. The zero
   module is finite projective (a summand of the finite free zero module), so
   `def-weil-pbc-smooth-ring-map` holds (Stacks 00U1).
-/
theorem finite_separable_multiplication_etale
    (k : Type u) (k' : Type v) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [Algebra.IsSeparable k k'] :
    let μ : k' ⊗[k] k' →ₐ[k] k' := Algebra.TensorProduct.lmul' k
    letI : Algebra (k' ⊗[k] k') k' := μ.toRingHom.toAlgebra
    Etale (Spec.map (CommRingCat.ofHom μ.toRingHom)) ∧
      Algebra.Smooth (k' ⊗[k] k') k' := by
  sorry

end AlgebraicGeometry
