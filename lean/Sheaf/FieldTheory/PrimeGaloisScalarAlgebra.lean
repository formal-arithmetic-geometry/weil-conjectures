/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Artinian.Module
import Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced
import WeilConjectures.AlgebraicGeometry.TensorGaloisPrimeTransitivity

/-!
# Scalar extension of a prime-degree Galois field

Source: Stacks Project, More on Algebra, Tag 09F4, proof, second paragraph,
implicit split-or-degree-prime field-algebra input.
(blueprint: lem-sfb-epp-prime-galois-scalar-algebra).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- Scalar extension of a prime-degree finite Galois extension is reduced and is
 either a Galois field of the same degree or a completely split algebra.
 Both alternatives use the canonical right scalar map `l ↦ 1 ⊗ₜ l`, supplied by
 `Algebra.TensorProduct.rightAlgebra`. The field structure `h.toField` retains
 the tensor ring operations and only supplies inverses.

Source: Stacks Project, More on Algebra, Tag 09F4, proof, second paragraph
(the general field-algebra input implicit there).
(blueprint: lem-sfb-epp-prime-galois-scalar-algebra).

Proof:
1. Swap factors to `U = L ⊗[F] E`. By `lem-pc-finrank-field-base-change`, its
   dimension over `L` is `p`. By `lem-weil-pbc-finite-separable-tensor-field-reduced`,
   it is reduced. Since `p > 0`, it is nonzero.
2. By `lem-weil-pbc-finite-dim-algebra-artinian`, `U` is Artinian. Apply
   `lem-sfb-reduced-artinian-residue-product` to identify it canonically with the
   finite product of its maximal-ideal residue fields. There are `r > 0` factors,
   and each is finite-dimensional over `L`, since the quotient of a spanning
   finite family still spans.
3. All maximal ideals contract to zero in `L`. Apply
   `lem-weil-pbc-tensor-galois-prime-transitivity`. Its automorphism of `E` acts
   on the second tensor factor and fixes `L`, inducing `L`-algebra isomorphisms
   between any two residue fields. Thus their degrees are one common `d > 0`.
4. Coordinatewise bases of the factors give `p = r * d`. Primality gives either
   `r = 1, d = p` or `r = p, d = 1`.
5. In the first case `U` is its unique residue field. The images of `E` and `L`
   generate it: every pure tensor is a product of elements from the two images.
   Apply `lem-sfb-galois-compositum-restriction` to see that this field is Galois
   over `L`. Its degree is `p`.
6. In the second case each scalar map from `L` to a residue field is bijective,
   because it is injective and the target has dimension one. Enumerating the
   `p` maximal ideals gives the `L`-algebra equivalence with `Fin p → L`.
   Transport both alternatives back through the tensor swap. -/
theorem prime_galois_scalar_algebra
    (F : Type u) (E : Type v) (L : Type w)
    [Field F] [Field E] [Field L] [Algebra F E] [Algebra F L]
    [FiniteDimensional F E] [IsGalois F E]
    (p : ℕ) (hp : p.Prime) (hdegree : Module.finrank F E = p) :
    IsReduced (E ⊗[F] L) ∧
      ((∃ h : IsField (E ⊗[F] L),
          @IsGalois L _ (E ⊗[F] L) h.toField
            (rightAlgebra (R := F) (A := E) (B := L)) ∧
          @Module.finrank L (E ⊗[F] L) _ _
            (rightAlgebra (R := F) (A := E) (B := L)).toModule = p) ∨
        Nonempty (@AlgEquiv L (E ⊗[F] L) (Fin p → L) _ _ _
          (rightAlgebra (R := F) (A := E) (B := L)) _)) := by
  sorry

end Algebra.TensorProduct
