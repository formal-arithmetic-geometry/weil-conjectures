/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Pairwise eventual agreement of inverse-image representatives -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

/-- Two affine local representatives with the same inverse-image section agree over
some later stage, without constructing or choosing a covering refinement.
Source: Stacks Project, Tags 03Q6 and 09XM, equality-open and limit-containment arguments.
(blueprint: lem-weil-pbc-affine-open-inverse-image-compatible-refinement-compatibility).

Proof: Form the affine overlap of V and W over D(j) and subtract the restricted
sections. After base change to the limit its unit is zero, by naturality of the unit
and the uniqueness of maps to the terminal object. Localize the adjunction to that
base-changed overlap; the zero-neighbourhood theorem gives an open containing its
limit image on which the difference is zero. On the cofiltered tail over j, the
base-changed overlaps form an affine-transition diagram of compact affine schemes.
Its limit is the base change of the overlap to c.pt, by the pullback universal
property. Eventual containment in the agreement open supplies k and f:k→j.
Any test object with a map to D(k) and compatible maps to V and W maps to this
base-changed overlap, so restriction of the zero difference gives the equality.
For an empty overlap all sections are zero; no nonemptiness assumption is used. -/
theorem affineOpenSections_pair_eventual_agreement
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
    (t : (H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt))))
    (j : J) (V W : X.Etale) (v : V ⟶ D.obj j) (w : W ⟶ D.obj j)
    (s : F.obj.obj (op V)) (r : F.obj.obj (op W))
    (πV : p.Etale.obj V ⟶ Scheme.Etale.mk (𝟙 c.pt))
    (πW : p.Etale.obj W ⟶ Scheme.Etale.mk (𝟙 c.pt))
    (hV : IsAffine V.left) (hW : IsAffine W.left)
    (hs : (H.obj F).obj.map πV.op t = (hH.unit.app F).hom.app (op V) s)
    (hr : (H.obj F).obj.map πW.op t = (hH.unit.app F).hom.app (op W) r) :
    ∃ (k : J) (f : k ⟶ j),
      ∀ (U : X.Etale) (a : U ⟶ V) (a' : U ⟶ W) (q : U ⟶ D.obj k),
        a ≫ v = q ≫ D.map f → a' ≫ w = q ≫ D.map f →
        F.obj.map a.op s = F.obj.map a'.op r := by sorry
