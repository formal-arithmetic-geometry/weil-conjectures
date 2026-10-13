/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Hypercover.Homotopy

/-! # Two covering morphisms induce the same zeroth Cech map

Source: literature/stacks-project/sites.tex, Sites, Lemma 00W7 and Remark 00W8
(blueprint: lem-weil-pbc-site-covering-morphisms-same-h0-map).
-/

@[expose] public section

universe w v u

namespace CategoryTheory.PreOneHypercover

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C]

/-- Two morphisms of coverings over the same base morphism induce the same map on
zeroth Cech compatible families.  In the fibre-product encoding of coverings,
this is the homotopy equality of the two induced multifork maps.

Source: literature/stacks-project/sites.tex, Sites, Lemma 00W7 and Remark 00W8
(blueprint: lem-weil-pbc-site-covering-morphisms-same-h0-map).
The proof is the universal-property argument of 00W7: the maps into each
fibre product give a homotopy, and the compatibility condition on a multifork
identifies the two components; `Homotopy.mapMultiforkOfIsLimit_eq` then gives
the equality.
-/
theorem siteCoveringMorphismsSameH0Map
    {S : C} {E F : PreOneHypercover.{w} S} {f g : E.Hom F}
    (H : Homotopy f g) (P : Cᵒᵖ ⥤ Type u)
    {c : Multifork (E.multicospanIndex P)} (hc : IsLimit c)
    (d : Multifork (F.multicospanIndex P)) :
    f.mapMultiforkOfIsLimit P hc d = g.mapMultiforkOfIsLimit P hc d := by
  sorry

end CategoryTheory.PreOneHypercover
