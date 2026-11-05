/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilFiniteKoszulTensorModel

/-! # Exterior multiplication for splitting the first Koszul generator

Source: Stacks Project, More on Algebra, Tag 0664,
lemma-join-sequences-koszul-complex.
(blueprint: def-weil-pbc-koszul-join-graded).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A]

/-- Wedge multiplication after the head and tail inclusions, in fixed exterior degrees.
Source: Stacks, Tag 0664 (blueprint: def-weil-pbc-koszul-join-graded). -/
@[irreducible] def koszulJoinWedge (r n k : ℕ) :
    (⋀[A]^n (Fin 1 →₀ A) ⊗[A] ⋀[A]^k (Fin r →₀ A)) →ₗ[A]
      ⋀[A]^(n + k) (Fin (r + 1) →₀ A) :=
  (koszulExteriorMul (r + 1) n k).comp
    (TensorProduct.map (exteriorPower.map n (koszulHeadInclusion r))
      (exteriorPower.map k (koszulTailInclusion r)))

end AlgebraicGeometry.Scheme
