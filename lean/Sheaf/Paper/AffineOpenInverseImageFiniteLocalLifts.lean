/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Finite local lifts at an affine open stage -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

/-- A terminal inverse-image section has finitely many affine local lifts at one stage.
Source: Stacks Project, Tags 09XN (local inverse-image sections), 0EYL (descent of
objects, arrows and finite covers), and 03Q6, proof steps (1)--(3).
(blueprint: lem-weil-pbc-affine-open-inverse-image-finite-local-lifts).

Proof: Fix an affine open stage and reindex its cofiltered tail by a directed order.
On the affine limit, inverse-image sheafification gives local unit representatives.
Refine their cover by a finite affine etale cover. Descend these covering objects,
their maps to the representing etale base objects, and the finite cover to one
later stage. Each descended affine object is etale over that open stage and hence
etale over X. Restrict the representing sections along the descended maps to obtain
s. Localization of inverse image along each open stage is restriction, so its unit
is precisely the restriction map. Unit naturality gives the displayed local
identities for the supplied H; uniqueness of left adjoints transports the standard
unit calculation to hH. Canonical pullback comparisons supply the arrows pi.
There is no agreement assertion on overlaps at this stage. For an empty limit,
descend the empty finite cover to an empty stage; the empty family of sections
then works. Singleton diagrams reduce to the open localization adjunction and
zero coefficients give zero representatives. -/
theorem affineOpenSections_inverse_image_finite_local_lifts
    {X : Scheme.{u + 1}} {J : Type (u + 1)} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ X.Etale)
    [∀ j, IsAffine (D.obj j).left] [∀ j, IsOpenImmersion (D.obj j).hom]
    (c : Cone (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X))
    (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ (D.obj j).hom = p)
    (hc : IsLimit c)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology c.pt.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (t : (H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))) :
    ∃ (j : J) (B : Type (u + 1)) (_ : Finite B)
      (V : B → X.Etale) (v : ∀ b, V b ⟶ D.obj j)
      (s : ∀ b, F.obj.obj (op (V b)))
      (π : ∀ b, p.Etale.obj (V b) ⟶ Scheme.Etale.mk (𝟙 c.pt)),
      (∀ b, IsAffine (V b).left) ∧
      Sieve.ofArrows V v ∈ X.smallEtaleTopology (D.obj j) ∧
      Sieve.ofArrows (fun b ↦ p.Etale.obj (V b)) π ∈
        c.pt.smallEtaleTopology (Scheme.Etale.mk (𝟙 c.pt)) ∧
      ∀ b, (H.obj F).obj.map (π b).op t =
        (hH.unit.app F).hom.app (op (V b)) (s b) := by sorry
