/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.FieldTheory.Separable
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres

/-!
# Algebraic separable extensions as filtered colimits of finite smooth algebras

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/
lem-kun-algebraic-separable-smooth.md, node lem-kun-algebraic-separable-smooth, order 1756
(blueprint: lem-kun-algebraic-separable-smooth).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace FieldTheory

/-- An algebraic separable field extension is a filtered colimit of finite separable,
and hence smooth, `K`-algebras.

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/
lem-kun-algebraic-separable-smooth.md, node lem-kun-algebraic-separable-smooth, order 1756
(the algebraic case of Stacks Project, Algebra, Lemma 10.158.11, Tag 07BV)
(blueprint: lem-kun-algebraic-separable-smooth).

Proof (node, step by step):
1. For every `x : L` the field `K(x)` is finite over `K`, because `L/K` is algebraic.
2. Given finite subextensions `E₁, E₂ ⊆ L`, the compositum `E₁E₂` is finite over `K` and
   contains both; so the finite subextensions form a filtered poset whose union is `L`,
   and `L` is their filtered colimit (inclusions as transition maps).
3. Each finite subextension is separable over `K` because `L/K` is.
4. By `lem-weil-pbc-finite-separable-extension-etale` (`Algebra.Etale.of_finite_of_isSeparable`)
   each stage is etale over `K`.
5. By `lem-weil-pbc-etale-smooth-zero-dimensional-fibres` an etale morphism is smooth
   (`def-sbc-smooth-morphisms`, of relative dimension zero), so each stage is a smooth
   `K`-algebra; the same filtered system exhibits `L` as a filtered colimit of smooth
   `K`-algebras.
-/
theorem algebraic_separable_extension_is_filtered_colimit_smooth
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [Algebra.IsSeparable K L] :
    CategoryTheory.ObjectProperty.ind.{v}
      (fun B : CommAlgCat.{v} K ↦
        IsField B ∧ Module.Finite K B ∧ Algebra.IsSeparable K B ∧ Algebra.Smooth K B)
      (CommAlgCat.of K L) := by
  sorry

end FieldTheory
