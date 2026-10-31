/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SolvableGroupStructure

/-! # Split additive series

Source: Milne, Algebraic Groups (2017), Definition 14.61 and paragraph 14.62, p.299.
(blueprint: def-sfb-split-unipotent-series)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth connected split additive series, with actual represented G_a quotients.
The zero-length series is the trivial group, so the trivial unipotent group is included.
Source: Milne, Definition 14.61 and paragraph 14.62, p.299.
(blueprint: def-sfb-split-unipotent-series) -/
def SplitUnipotentLength {k : Type u} [Field k]
    (U : Grp (Over (Spec (.of k)))) (n : ℕ) : Prop :=
  match n with
  | 0 => Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ Nonempty (U ≅ Grp.trivial _)
  | n + 1 => Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧
      ∃ (N : Grp (Over (Spec (.of k)))) (i : N ⟶ U)
        (q : U ⟶ Grp.mk (StandardGroupSchemes.additive k)),
        IsClosedSubgroupScheme i.hom.hom ∧ IsNormalSubgroupScheme i.hom.hom ∧
        SolvableGroupStructure.IsFppfQuotient i.hom.hom q ∧ SplitUnipotentLength N n

end AlgebraicGeometry
