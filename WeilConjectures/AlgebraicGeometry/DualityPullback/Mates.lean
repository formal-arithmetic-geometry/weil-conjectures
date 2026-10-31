/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The adjoint transform of a contravariant exchange -/

@[expose] public section
set_option autoImplicit false

open CategoryTheory Opposite

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]
  {F : D ⥤ C} {G : C ⥤ D} {P : C ⥤ D} {R : D ⥤ C}
  {DX : Cᵒᵖ ⥤ C} {DY : Dᵒᵖ ⥤ D}

/-- The adjoint transform of `DY P ≅ G DX` is constructed by uniqueness of right
adjoints. Source: cor-sf-duality-pullback, passing to adjoints.
(blueprint: lem-sf-duality-pullback-adjoint-transform). -/
def dualityPullbackMate (sX : DX.rightOp ⊣ DX) (sY : DY.rightOp ⊣ DY)
    (a : F ⊣ G) (b : P ⊣ R) (e : P.op ⋙ DY ≅ DX ⋙ G) :
    F.op ⋙ DX ≅ DY ⋙ R :=
  (((sX.rightOp.comp a.op).ofNatIsoLeft
    { hom := e.hom.rightOp
      inv := e.inv.rightOp
      hom_inv_id := by
        ext A
        apply Quiver.Hom.unop_inj
        exact e.inv_hom_id_app (op A)
      inv_hom_id := by
        ext A
        apply Quiver.Hom.unop_inj
        exact e.hom_inv_id_app (op A) }).rightAdjointUniq (b.comp sY))

private lemma comparison_hom {E : Type*} [Category E] {L : C ⥤ E}
    {H H' : E ⥤ C} (a : L ⊣ H) (b : L ⊣ H') (A : C) (B : E)
    (h : A ⟶ H.obj B) :
    h ≫ (a.rightAdjointUniq b).hom.app B =
      b.homEquiv A B ((a.homEquiv A B).symm h) := by
  apply (b.homEquiv A B).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_symm_rightAdjointUniq_hom_app, Equiv.symm_apply_apply]
  rfl

/-- Its action on Hom sets is the two transposes and the two ordinary adjunctions,
with the inverse exchange between them. Source: the explicit five-arrow chain in
cor-sf-duality-pullback. (blueprint: lem-sf-duality-pullback-adjoint-transform). -/
theorem dualityPullbackMate_hom (sX : DX.rightOp ⊣ DX) (sY : DY.rightOp ⊣ DY)
    (a : F ⊣ G) (b : P ⊣ R) (e : P.op ⋙ DY ≅ DX ⋙ G)
    (A : C) (B : D) (h : A ⟶ DX.obj (op (F.obj B))) :
    h ≫ (dualityPullbackMate sX sY a b e).hom.app (op B) =
      b.homEquiv A (DY.obj (op B))
        (sY.homEquiv (P.obj A) (op B)
          ((a.homEquiv B (DX.obj (op A))
            (sX.homEquiv (F.obj B) (op A) h.op) ≫ e.inv.app (op A)).op)) := by
  let i : DX.rightOp ⋙ G.op ≅ P ⋙ DY.rightOp :=
    { hom := e.hom.rightOp
      inv := e.inv.rightOp
      hom_inv_id := by
        ext A
        apply Quiver.Hom.unop_inj
        exact e.inv_hom_id_app (op A)
      inv_hom_id := by
        ext A
        apply Quiver.Hom.unop_inj
        exact e.hom_inv_id_app (op A) }
  let adj := (sX.rightOp.comp a.op).ofNatIsoLeft i
  have hc := comparison_hom adj (b.comp sY) A (op B) h
  change h ≫ (adj.rightAdjointUniq (b.comp sY)).hom.app (op B) = _
  rw [hc]
  dsimp only [adj]
  simp only [Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
  simp only [Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  dsimp [Adjunction.homEquiv, Adjunction.op, Adjunction.rightOp, i]

/-- The same Hom formula written using only the units of the self-adjunctions.
Proof: expand the two self-adjunction Hom equivalences in the preceding formula.
Source: cor-sf-duality-pullback, the two evaluation transposes.
(blueprint: lem-sf-duality-pullback-adjoint-transform). -/
theorem dualityPullbackMate_hom_unit (sX : DX.rightOp ⊣ DX) (sY : DY.rightOp ⊣ DY)
    (a : F ⊣ G) (b : P ⊣ R) (e : P.op ⋙ DY ≅ DX ⋙ G)
    (A : C) (B : D) (h : A ⟶ DX.obj (op (F.obj B))) :
    h ≫ (dualityPullbackMate sX sY a b e).hom.app (op B) =
      b.homEquiv A (DY.obj (op B))
        (sY.unit.app (P.obj A) ≫ DY.map
          ((a.homEquiv B (DX.obj (op A))
            (sX.unit.app (F.obj B) ≫ DX.map h.op)) ≫ e.inv.app (op A)).op) := by
  rw [dualityPullbackMate_hom]
  rfl

/-- Substitute specified transpose units in the Hom formula before specialization.
Proof: rewrite the two unit components in the unit-only formula.
Source: cor-sf-duality-pullback, evaluation transposition.
(blueprint: lem-sf-duality-pullback-adjoint-transform). -/
theorem dualityPullbackMate_hom_of_units (sX : DX.rightOp ⊣ DX) (sY : DY.rightOp ⊣ DY)
    (a : F ⊣ G) (b : P ⊣ R) (e : P.op ⋙ DY ≅ DX ⋙ G)
    (A : C) (B : D) (h : A ⟶ DX.obj (op (F.obj B)))
    (δX : F.obj B ⟶ DX.obj (op (DX.obj (op (F.obj B)))))
    (δY : P.obj A ⟶ DY.obj (op (DY.obj (op (P.obj A)))))
    (hX : sX.unit.app (F.obj B) = δX) (hY : sY.unit.app (P.obj A) = δY) :
    h ≫ (dualityPullbackMate sX sY a b e).hom.app (op B) =
      b.homEquiv A (DY.obj (op B))
        (δY ≫ DY.map ((a.homEquiv B (DX.obj (op A))
          (δX ≫ DX.map h.op)) ≫ e.inv.app (op A)).op) := by
  rw [dualityPullbackMate_hom_unit, hX, hY]

/-- Restricting a natural isomorphism to a full subcategory preserves its Hom action.
Proof: the inclusion sends an object to its underlying object, and whiskering evaluates
components there. Source: the finite-Tor restriction in cor-sf-duality-pullback.
(blueprint: lem-sf-duality-pullback-adjoint-transform). -/
theorem dualityPullbackRestrict_hom (Q : ObjectProperty D) {U V : Dᵒᵖ ⥤ C}
    (e : U ≅ V) (A : C) (B : Q.FullSubcategory) (h : A ⟶ U.obj (op B.obj)) :
    h ≫ (Functor.isoWhiskerLeft Q.ι.op e).hom.app (op B) =
      h ≫ e.hom.app (op B.obj) := by
  rfl

/-- The restriction Hom formula also applies to an isomorphism identified with it.
Proof: substitute the equality of isomorphisms in the restriction formula.
Source: identifying the chosen comparison in cor-sf-duality-pullback.
(blueprint: lem-sf-duality-pullback-adjoint-transform). -/
theorem dualityPullbackRestrict_hom_of_eq (Q : ObjectProperty D) {U V : Dᵒᵖ ⥤ C}
    (e : U ≅ V) (j : Q.ι.op ⋙ U ≅ Q.ι.op ⋙ V)
    (hj : j = Functor.isoWhiskerLeft Q.ι.op e)
    (A : C) (B : Q.FullSubcategory) (h : A ⟶ U.obj (op B.obj)) :
    h ≫ j.hom.app (op B) = h ≫ e.hom.app (op B.obj) := by
  subst j
  exact dualityPullbackRestrict_hom Q e A B h

/-- An ambient Hom formula transports to an identified restriction.
Proof: compose the restriction formula with the specified ambient formula.
Source: finite-Tor restriction in cor-sf-duality-pullback.
(blueprint: lem-sf-duality-pullback-adjoint-transform). -/
theorem dualityPullbackRestrict_hom_of_formula (Q : ObjectProperty D) {U V : Dᵒᵖ ⥤ C}
    (e : U ≅ V) (j : Q.ι.op ⋙ U ≅ Q.ι.op ⋙ V)
    (hj : j = Functor.isoWhiskerLeft Q.ι.op e)
    (A : C) (B : Q.FullSubcategory) (h : A ⟶ U.obj (op B.obj))
    (q : A ⟶ V.obj (op B.obj)) (hq : h ≫ e.hom.app (op B.obj) = q) :
    h ≫ j.hom.app (op B) = q := by
  exact (dualityPullbackRestrict_hom_of_eq Q e j hj A B h).trans hq

end CategoryTheory
