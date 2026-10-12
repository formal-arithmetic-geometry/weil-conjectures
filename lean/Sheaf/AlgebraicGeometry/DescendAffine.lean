/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Affineness descends to a finite stage

Source: Stacks Project, Limits, Lemma 01ZN in Situation 081D
(blueprint: lem-weil-pbc-descend-affine).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Limits, Lemma 01ZN in Situation 081D
(blueprint: lem-weil-pbc-descend-affine).
An affine base change to the inverse limit is affine at some stage above the chosen index.
The structure morphism of `X₀` is `f₀ ≫ h`, so `f₀` is a morphism over the chosen base.

Proof:
1. The transition maps and limit projections are affine
   (lem-weil-pbc-limit-affine-transition). Their base changes are affine
   (lem-weil-pbc-affine-morphism-permanence). Cartesian-square pasting identifies the
   induced map with the base change of f₀ (lem-weil-pbc-cartesian-square-pasting).
   Since X₀ and Y₀ are qcqs, these maps are qcqs
   (lem-weil-pbc-qcqs-morphism-permanence).
2. Choose a finite affine open cover Vⱼ,₀ of Y₀ (def-pc-scheme and
   def-weil-pbc-scheme-conventions). Its preimages Vⱼ,T cover each base-changed target
   and are affine. Put Uⱼ,T = f_T⁻¹(Vⱼ,T). They are qcqs by
   lem-weil-pbc-open-preimage-fibre-product and lem-weil-pbc-qcqs-over-affine.
3. At the limit, Uⱼ is affine since f is affine (pqf-def-affine-morphism).
4. Each Uⱼ is the limit of Uⱼ,i over the upper tail, with affine transitions
   (lem-weil-pbc-scheme-over-limit and lem-weil-pbc-limit-cone-affine-projections-opens).
5. Each Uⱼ,i is affine for all sufficiently large i (lem-weil-pbc-limit-affine-stage).
6. Directedness gives a common index for the finitely many j. At that index all the
   preimages of the affine cover are affine, so f_i is affine
   (pqf-lem-affine-local-target). For the empty cover take the chosen index itself. -/
theorem exists_isAffineHom_baseChange_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    {X₀ Y₀ : Scheme.{u}} [CompactSpace X₀] [QuasiSeparatedSpace X₀]
    [CompactSpace Y₀] [QuasiSeparatedSpace Y₀]
    (f₀ : X₀ ⟶ Y₀) (h : Y₀ ⟶ D.obj (op i₀))
    (hf : IsAffineHom
      (pullback.map (f₀ ≫ h) (c.π.app (op i₀)) h (c.π.app (op i₀))
        f₀ (𝟙 c.pt) (𝟙 (D.obj (op i₀)))
        (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm))) :
    ∃ (i : I) (hi : i₀ ≤ i), IsAffineHom
      (pullback.map (f₀ ≫ h) (D.map (homOfLE hi).op) h (D.map (homOfLE hi).op)
        f₀ (𝟙 (D.obj (op i))) (𝟙 (D.obj (op i₀)))
        (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) := by
  sorry

end AlgebraicGeometry
