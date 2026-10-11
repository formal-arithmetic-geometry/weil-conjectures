/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.FieldTheory.SeparableExtension

/-!
# Separably generated field extensions are separable

Source: Stacks Project, Algebra, Lemma 10.44.3 (Tag 030X)
(blueprint: lem-weil-pbc-separably-generated-separable).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A separably generated field extension is separable: every finitely generated intermediate
field is separably generated over the base field.
Source: Stacks Project, Algebra, Lemma 10.44.3 (Tag 030X), with Definition 10.42.1 (Tag 030O)
(blueprint: lem-weil-pbc-separably-generated-separable).

Proof:
1. Split according to the characteristic of `k`. In characteristic zero, every field extension
   is separable by `lem-weil-pbc-char-zero-field-extension-separable`.
2. In prime characteristic, let `L/k` be any field extension. Since `L` is reduced, apply
   `lem-weil-pbc-separably-generated-tensor-reduced` (Tag 030U) to the separably generated
   extension `K/k` and the reduced algebra `L`. Thus `K ⊗[k] L` is reduced for every `L`.
3. Apply `lem-weil-pbc-geometrically-reduced-extension-separable` (Tag 030W, (4) implies (1))
   to obtain separability of `K/k`: each finitely generated intermediate field is separably
   generated, precisely clause (2) of `def-weil-pbc-separable-field-extension`.
-/
theorem isSeparableExtension_of_isSeparablyGenerated
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (h : Algebra.IsSeparablyGenerated k K) : Algebra.IsSeparableExtension k K := by
  sorry

end Algebra
