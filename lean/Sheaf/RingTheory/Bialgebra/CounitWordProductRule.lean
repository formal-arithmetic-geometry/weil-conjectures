/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.Pi
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Ordered convolution words of counit derivations

Source: Milne, Algebraic Groups (2017), Sections 11e, 11.24--11.26, printed pp.216--218,
and Lemma 11.27, printed p.218; extracted ordered product-rule calculation
(blueprint: lem-sfb-bialgebra-counit-word-product-rule).

The bialgebra structure packages the specified unital algebra coproduct and counit,
coassociativity and both counit identities. `WithConv` carries Mathlib's convolution.
Filtering `List.finRange r` preserves the increasing order of every fibre.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Bialgebra

/-- Ordered convolution products of derivations at the counit satisfy the product rule
indexed by all assignments of the derivations to the input factors. The empty word is
Mathlib's convolution unit, hence the counit. Only the scalar products are commutative;
the convolution words retain their increasing index order.

Source: Milne, Algebraic Groups (2017), Sections 11e, 11.24--11.26, printed pp.216--218,
and Lemma 11.27, printed p.218; extracted prerequisite for evaluation at the identity
(blueprint: lem-sfb-bialgebra-counit-word-product-rule).

Proof:
1. Apply lem-sfb-convolution-linear-map-algebra with R = B = k. Convolution is
   associative with unit the counit. For r = 0 the unique assignment has empty fibres,
   and the formula is multiplicativity of the counit on the product.
2. Induct on the number m of input factors to expand each binary counit derivation
   rule as v(y_1 ... y_m) = sum_j v(y_j) prod_{ell != j} counit(y_ell).
3. For the induction from r to r+1, write each coproduct Delta(c_j) as a finite sum
   of pure tensors x_{j,alpha} tensor y_{j,alpha}, using
   def-weil-pbc-module-tensor-product. Multiplicativity of Delta and finite
   distributivity express the convolution evaluation as the sum over alpha tuples
   of W_{all old indices}(prod_j x_j) v_{r+1}(prod_j y_j).
4. Apply the word-length induction hypothesis to the x factors and step 2 to the y
   factors. Distribute the finite sums, indexed by an old assignment f and a factor j.
   Rearrange only scalar factors in k; do not exchange any convolution factors.
5. Factor the sums over independent alpha indices. The j factor is
   (W_{fibre j} * v_{r+1})(c_j), and every other factor is
   (W_{fibre ell} * counit)(c_ell). The convolution unit identities from
   lem-sfb-convolution-linear-map-algebra remove the latter counits. Appending the
   greatest index r+1 to fibre j gives its ordered word, including an empty old fibre.
6. Reindex by the bijection between pairs (old assignment f, chosen factor j) and
   assignments on r+1 indices. This proves the induction step while preserving every
   fibre's increasing order. No antipode, cocommutativity, finite generation or
   characteristic assumption enters the calculation. -/
theorem counit_word_product_rule
    (k : Type u) (C : Type v) [Field k] [CommRing C] [Bialgebra k C]
    (r : ℕ) (v : Fin r → C →ₗ[k] k)
    (hv : ∀ (i : Fin r) (c d : C),
      v i (c * d) = Coalgebra.counit c * v i d + v i c * Coalgebra.counit d)
    (m : ℕ) (hm : 1 ≤ m) (c : Fin m → C) :
    (List.ofFn (fun i : Fin r ↦ WithConv.toConv (v i))).prod (∏ j, c j) =
      ∑ f : Fin r → Fin m, ∏ j : Fin m,
        (((List.finRange r).filter (fun i ↦ f i == j)).map
          (fun i ↦ WithConv.toConv (v i))).prod (c j) := by
  sorry

end Bialgebra
