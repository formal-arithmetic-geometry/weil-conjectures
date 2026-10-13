/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Descent of a representing etale cover in an affine open system

Source: Stacks Project, Tags 0EYL and 03Q6, finite objects, maps and cover descent.
(blueprint: lem-weil-pbc-affine-open-representing-cover-descent). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

/-- Refine a covering with representing maps and descend its geometric data.
Source: Stacks Project, Tag 0EYL, finite diagram and finite cover descent;
Tag 03Q6, proof steps (1)--(3); Tag 01ZM, morphism descent.
(blueprint: lem-weil-pbc-affine-open-representing-cover-descent).

Proof: Fix one affine open stage and reindex its cofiltered tail by a
directed coinitial system. The limit is affine. Refine the Z-cover by a finite
affine etale cover, retaining each source's map to a selected Z_i and hence
its representing arrow to p^*W_i. Use the terminal etale object at the fixed
stage as the fixed affine target. Pull back each W_i to that stage; these
etale objects need not be quasi-compact. Canonical pullback comparisons and
p = (limit projection) followed by (stage immersion) convert the finite
covering maps and representing arrows into the input of
etale_finiteCoverFactorizationDescent. It descends affine sources and both
families of maps to a common later stage, makes the stage family covering,
and retains the equations under one common source comparison. Its proof
uses the base-change diagram of each affine source model and locally finite
presentation of W_i to descend representing maps, so no quasi-compactness
of W_i or X is imposed. Identify the stage pullback of the fixed terminal
object with the stage terminal object. Compose model structure maps with
the stage immersion to obtain the X-objects V_b. Compose representing maps
with the pullback projections to obtain w_b, and the source comparisons
with the original refinement maps to obtain e_b. Pullback hom_ext proves
p^*(w_b)=e_b followed by a_{r(b)}. The composites with z_{r(b)} recover the
refining limit cover, and the stage covering property survives terminal
comparison and composition into X. For an empty limit the same finite
cover descent makes an empty stage. No sheaves or sections are involved. -/
theorem affineOpen_representing_cover_descent
    {X : Scheme.{u + 1}} {J : Type (u + 1)} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ X.Etale)
    [∀ j, IsAffine (D.obj j).left] [∀ j, IsOpenImmersion (D.obj j).hom]
    (c : Cone (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X))
    (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ (D.obj j).hom = p)
    (hc : IsLimit c)
    (I : Type (u + 1)) (Z : I → c.pt.Etale)
    (z : ∀ i, Z i ⟶ Scheme.Etale.mk (𝟙 c.pt))
    (W : I → X.Etale) (a : ∀ i, Z i ⟶ p.Etale.obj (W i))
    (hz : Sieve.ofArrows Z z ∈
      c.pt.smallEtaleTopology (Scheme.Etale.mk (𝟙 c.pt))) :
    ∃ (j : J) (B : Type (u + 1)) (_ : Finite B) (r : B → I)
      (V : B → X.Etale) (v : ∀ b, V b ⟶ D.obj j)
      (w : ∀ b, V b ⟶ W (r b)) (e : ∀ b, p.Etale.obj (V b) ⟶ Z (r b)),
      (∀ b, IsAffine (V b).left) ∧
      Sieve.ofArrows V v ∈ X.smallEtaleTopology (D.obj j) ∧
      Sieve.ofArrows (fun b ↦ p.Etale.obj (V b)) (fun b ↦ e b ≫ z (r b)) ∈
        c.pt.smallEtaleTopology (Scheme.Etale.mk (𝟙 c.pt)) ∧
      ∀ b, p.Etale.map (w b) = e b ≫ a (r b) := by
  sorry
