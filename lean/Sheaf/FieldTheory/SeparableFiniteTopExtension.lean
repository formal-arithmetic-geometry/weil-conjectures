/-
Copyright (c) 2026 Weil Conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil Conjectures project
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import WeilConjectures.FieldTheory.SeparableExtension
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced
import WeilConjectures.FieldTheory.GeometricallyReducedExtensionSeparable

/-!
# Finite separable top extensions preserve nonalgebraic separability

Source: Stacks Project, More on Algebra, Tag 0BRM, `lemma-abhyankar`, final paragraph;
Algebra, Tags 030O, 030U, and 030W
(blueprint: lem-sfb-separable-finite-top-extension).
-/

@[expose] public section

universe u v w

namespace Algebra

/-- For a tower `k ⊆ L ⊆ M`, if `L/k` is separable in the possibly transcendental sense
and `M/L` is finite separable algebraic, then `M/k` is separable in that same sense.
No algebraicity or finite generation of `L/k` is assumed.

Source: Stacks Project, More on Algebra, Tag 0BRM, `lemma-abhyankar`, final paragraph;
Algebra, Definition Tag 030O and Lemmas Tags 030U and 030W
(blueprint: lem-sfb-separable-finite-top-extension).

Proof:
1. In characteristic zero, apply `lem-weil-pbc-char-zero-field-extension-separable`
   directly to `M/k`. Otherwise the characteristic of `k` is a prime `p`. For an arbitrary
   field extension `E/k`, put `S = L ⊗[k] E`, using the commutative algebra structures of
   `lem-weil-pbc-algebra-tensor-pushout-universal-property`.
2. Show `S` is reduced. A nilpotent `z` is a finite sum of pure tensors, by
   `def-weil-pbc-module-tensor-product`. The finitely many coefficients from `L` generate
   a finitely generated intermediate field `F/k`. The hypothesis `hL` makes `F/k`
   separably generated (`def-weil-pbc-separable-field-extension`), so `F ⊗[k] E` is
   reduced by `lem-weil-pbc-separably-generated-tensor-reduced`. The inclusion into
   `L ⊗[k] E` is injective by `lem-weil-pbc-module-over-field-flat` and
   `lem-trf-flat-tensor-preserves-injection` (interchanging tensor factors if necessary).
   The element `z` lifts to a sum `y` in `F ⊗[k] E`. Injectivity implies that a power of
   `y` is zero; reducedness gives `y = 0`, hence `z = 0`.
3. The empty family is a transcendence basis for the algebraic extension `M/L`, and its
   generated intermediate field is `L` (`def-weil-pbc-transcendence-basis`). Thus the
   separability assumption on `M/L` (`def-weil-pbc-separable-algebraic-extension`)
   makes it separably generated, by clause (1) of `def-weil-pbc-separable-field-extension`.
4. Apply `lem-weil-pbc-separably-generated-tensor-reduced` over `L` to `M` and the
   reduced `L`-algebra `S`. It makes `M ⊗[L] (L ⊗[k] E)` reduced. The ring isomorphism
   to `M ⊗[k] E` sends `m ⊗ (l ⊗ e)` to `m * l ⊗ e`, and its inverse sends
   `m ⊗ e` to `m ⊗ (1 ⊗ e)`. Tensor balancing makes the maps well-defined and
   multiplicative, and their composites are identities on pure tensors, hence everywhere
   by `def-weil-pbc-module-tensor-product`. Thus `M ⊗[k] E` is reduced.
5. Since `E/k` was arbitrary, apply
   `lem-weil-pbc-geometrically-reduced-extension-separable` in characteristic `p` to
   conclude that every finitely generated intermediate field of `M/k` is separably
   generated. This is exactly `IsSeparableExtension k M`.
-/
theorem isSeparableExtension_of_finite_separable_top
    (k : Type u) (L : Type v) (M : Type w)
    [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
    [FiniteDimensional L M] [Algebra.IsSeparable L M]
    (hL : IsSeparableExtension k L) : IsSeparableExtension k M := by
  sorry

end Algebra
