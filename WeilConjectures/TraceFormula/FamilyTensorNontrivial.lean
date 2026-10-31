/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import WeilConjectures.FieldTheory.FiniteFamilyTensorNontrivial

/-!
# Nontriviality of a small family tensor coproduct

Source: Stacks Project, `literature/stacks-project/limits.tex`, Tag 0CNJ
(blueprint: lem-trf-family-tensor-nontrivial).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

/-- The coproduct of a small family of field extensions of a field is nontrivial.

Source: Stacks Project, `literature/stacks-project/limits.tex`, Tag 0CNJ
(blueprint: lem-trf-family-tensor-nontrivial).

Proof: Regard the coproduct as the filtered colimit of its finite subcoproducts.
Each finite tensor coproduct is nontrivial, including the empty coproduct, which is
`k`.  For an inclusion of finite subsets, write the larger tensor as the smaller
one tensored with the remaining factors.  The structural map from the field `k`
to the remaining nontrivial tensor is injective, and tensoring this map with the
flat `k`-module given by the smaller tensor preserves injectivity.  Thus all
transition maps are injective.  Equality in the filtered-colimit presentation
then cannot identify `0` and `1` from the empty stage, so the full coproduct is
nontrivial.  The empty family is exactly the empty stage and gives `k`.
-/
theorem nontrivial_coproduct_of_field_extensions
    (k : Type u) [Field k] (J : Type w) (L : J → Type v)
    [∀ j : J, Field (L j)] [∀ j : J, Algebra k (L j)]
    (c : Cocone (Discrete.functor (fun j : J =>
      (CommAlgCat.of k (L j) : CommAlgCat.{v} k))))
    (hc : IsColimit c) : Nontrivial c.pt := by
  sorry

end CommAlgCat
