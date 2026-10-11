/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.FieldTheory.SeparableExtension
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Tensoring a reduced algebra with a separably generated field extension

Source: Stacks Project, Algebra, Lemma 10.43.6 (Tag 030U), separably generated case
(blueprint: lem-weil-pbc-separably-generated-tensor-reduced).
-/

universe u v w

open scoped TensorProduct

namespace Algebra

/-- Tensoring a reduced commutative `k`-algebra with a separably generated field extension
of `k` gives a reduced ring. Source: Stacks Project, Algebra, Lemma 10.43.6 (Tag 030U),
separably generated case (blueprint: lem-weil-pbc-separably-generated-tensor-reduced).

Proof:
1. Write a nilpotent tensor as a finite sum of pure tensors. Fix a separating transcendence
   basis. By `lem-weil-pbc-separating-transcendence-basis-finite-subextension`, its finitely
   many field coefficients lie in a finite separable extension `K'` of a rational function
   field `L = k(x_i : i ∈ T)` with `T` finite. Its algebra coefficients generate a reduced
   finite type subalgebra `S'`. Flatness over a field (`lem-weil-pbc-module-over-field-flat`
   and `def-weil-pbc-flat-ring-map`) makes the maps from `K' ⊗ S'` into `K ⊗ S` injective.
   Thus it suffices to prove reducedness for `K'` and `S'`.
2. The field `k` is Noetherian, and `S'` is Noetherian by
   `lem-weil-pbc-finite-type-algebra-noetherian`. By
   `lem-weil-pbc-reduced-noetherian-total-ring-fractions`, `S'` embeds in a finite product
   of fields. Flatness preserves this injection after tensoring with `K'`, and
   `lem-weil-pbc-tensor-finite-product` distributes tensoring over this finite product.
   Products and subrings of reduced rings are reduced, so reduce to a field factor `F/k`.
   If `S'` is the zero ring there are no factors and the conclusion is immediate.
3. By `lem-weil-pbc-polynomial-scalar-extension`, the polynomial ring over `k` on the
   finite independent family becomes a polynomial ring over `F`, which is a domain by
   `lem-weil-pbc-polynomial-ring-domain`. Localizing at the nonzero polynomials over `k`
   gives `L ⊗[k] F`, still a domain by
   `lem-weil-pbc-generic-fibre-localization-domain-irreducible`. Embed it in its fraction
   field `E`, which is a field extension of `L`.
4. Associativity identifies `K' ⊗[k] F` with `K' ⊗[L] (L ⊗[k] F)`. Flatness over `L`
   embeds this in `K' ⊗[L] E`, which is reduced by
   `lem-weil-pbc-finite-separable-tensor-field-reduced`. Reducedness descends to the
   subring, then to `K' ⊗[k] S'` by step 2. The nilpotent from step 1 is therefore zero,
   proving that `K ⊗[k] S` is reduced. -/
theorem isReduced_tensorProduct_of_isSeparablyGenerated
    (k : Type u) (K : Type v) (S : Type w)
    [Field k] [Field K] [CommRing S] [Algebra k K] [Algebra k S] [IsReduced S]
    (hK : IsSeparablyGenerated k K) : IsReduced (K ⊗[k] S) := by
  sorry

end Algebra
