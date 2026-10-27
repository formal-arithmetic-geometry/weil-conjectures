/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.TensorProduct.Maps

import Sheaf.FieldTheory.FamilyCommonExtensionFields
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Diagonal accumulation from infinitely many affine primes

Source: Stacks Project, Tag 088I (`lemma-infinite-number`) and the absolute tensor-product
convention in Tag 088J (blueprint: lem-sfb-infinite-primes-off-diagonal-closure).

The ambient tensor product is over the integers; only the residue fields are algebras over `k`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The canonical map `A ⊗[ℤ] A → κ(p) ⊗[k] κ(q)`, sending `a ⊗ b` to the tensor of
its residue evaluations at `p` and `q`. No `k`-algebra structure on `A` is needed.
Source: Stacks Project, Tag 088I (`lemma-infinite-number`)
(blueprint: lem-sfb-infinite-primes-off-diagonal-closure). -/
noncomputable def residueTensorMap (A : Type u) [CommRing A] (k : Type v) [Field k]
    (p q : Spec (CommRingCat.of A))
    [Algebra k ((Spec (CommRingCat.of A)).residueField p)]
    [Algebra k ((Spec (CommRingCat.of A)).residueField q)] :
    A ⊗[ℤ] A →+*
      (Spec (CommRingCat.of A)).residueField p ⊗[k]
        (Spec (CommRingCat.of A)).residueField q :=
  (Algebra.TensorProduct.productMap
    ((Algebra.TensorProduct.includeLeftRingHom.comp
      (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).Γevaluation p).hom)).toIntAlgHom)
    ((Algebra.TensorProduct.includeRight.toRingHom.comp
      (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).Γevaluation q).hom)).toIntAlgHom)).toRingHom

/-- The closure of the union of the off-diagonal residue-tensor images meets the absolute
 diagonal of an affine scheme with infinitely many distinct primes.
Source: Stacks Project, Tag 088I (`lemma-infinite-number`)
(blueprint: lem-sfb-infinite-primes-off-diagonal-closure).

Proof:
1. By [lem-trf-family-common-extension-field], embed all residue fields compatibly over `k`
   in a field `K`. Put `B = ℕ → K` and map `A` to `B` by the residue evaluations.
2. In `C = B ⊗[K] B`, let `e_n` be the coordinate idempotents. By
   [lem-sfb-sequence-tensor-off-diagonal-kernel], the kernel of the off-diagonal
   coordinate map to the product of `K` over `n ≠ m` is `J = (e_n ⊗ e_n)`.
   The coordinate kernels are primes, and their closure is `V(J)`: a closed set
   containing all those primes has defining ideal contained in their intersection `J`.
3. The ideal `I = (e_n)` in `B` is proper, since its elements have finite support,
   whereas `1` has infinite support. By [lem-weil-pbc-minimal-prime-over-proper-ideal],
   choose a prime containing `I`. Its inverse image under multiplication `C → B`
   contains `J`, hence belongs to the closure of the off-diagonal coordinate primes.
4. The map `A ⊗[ℤ] A → C` sends each such coordinate prime into the corresponding
   residue-tensor image: the compatible embeddings give `κ(p_n) ⊗[k] κ(p_m) → K`.
   Continuity sends the chosen point into the required closure. Its image also lies
   on the absolute diagonal, since multiplication after this map is the composite
   of multiplication `A ⊗[ℤ] A → A` with `A → B`.
The indexing set `ℕ` is the source's sequence indexed by positive integers, reindexed by `n + 1`.
-/
theorem infinitePrimes_offDiagonalClosure (A : Type u) [CommRing A]
    (k : Type v) [Field k] (p : ℕ → Spec (CommRingCat.of A))
    (hp : Function.Injective p)
    [∀ n : ℕ, Algebra k ((Spec (CommRingCat.of A)).residueField (p n))] :
    (closure (⋃ n : ℕ, ⋃ m : ℕ, ⋃ (_ : n ≠ m),
      Set.range (PrimeSpectrum.comap (residueTensorMap A k (p n) (p m)))) ∩
      Set.range (PrimeSpectrum.comap
        (Algebra.TensorProduct.lmul' ℤ (S := A)).toRingHom)).Nonempty := by
  sorry

end AlgebraicGeometry
