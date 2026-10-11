/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Separatedness descends to a finite stage

Source: Stacks Project, Limits, Lemma 01ZQ in Situation 081D
(blueprint: lem-weil-pbc-descend-separated).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- For a morphism between qcqs schemes over a qcqs stage of an inverse system with affine
transitions, separatedness after base change to the limit implies separatedness after
base change to some later stage. No finiteness assumption on the morphism is required.

Source: Stacks Project, Limits, Lemma 01ZQ in Situation 081D
(blueprint: lem-weil-pbc-descend-separated).

Proof:
1. The diagonal of the limit morphism is a closed immersion by separatedness
   (def-weil-proper-morphism). The stage diagonal is an immersion
   (lem-weil-pbc-diagonal-immersion, Schemes 01KJ), hence locally of finite type
   (lem-weil-pbc-immersion-base-change-lft, Morphisms 01T5). Its source and target are qcqs:
   a morphism between qcqs schemes is quasi-compact and quasi-separated, these properties
   survive base change, and composing with the qcqs structure morphism gives the qcqs
   fibre product (lem-weil-pbc-qcqs-morphism-permanence).
2. Apply closed-immersion descent (lem-weil-pbc-descend-closed-immersion, Limits 01ZP) to
   the stage diagonal. The canonical identifications between base changes of fibre products
   and fibre products of base changes preserve both projections and the diagonal
   (def-pc-fibre-product). Thus the diagonal at some later stage is a closed immersion,
   and the base-changed morphism there is separated (def-weil-proper-morphism). -/
theorem Scheme.exists_isSeparated_overPullbackMap
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀)))
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (f₀ : X₀ ⟶ Y₀)
    (hsep : IsSeparated (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (hi : i₀ ≤ i),
      IsSeparated (((Over.pullback (D.map (homOfLE hi).op)).map f₀).left) := by
  sorry

end AlgebraicGeometry
