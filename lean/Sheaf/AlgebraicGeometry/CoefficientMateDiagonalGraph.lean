/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-! # Diagonal and graph evaluation of coefficient mates

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-prop-sfb-cartesian-coefficients/lem-sfb-eta-comp.proof.md`, composition identity
and final fibre-product comparison (blueprint: lem-sfb-coefficient-mate-diagonal-graph).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

private theorem diagonal_graph_maps {B V W : Scheme.{u}}
    (f : V ⟶ B) (h : W ⟶ V) (w : W ⟶ B) (hw : w = h ≫ f)
    (hδ : (pullback.fst (𝟙 V) h ≫ pullback.diagonal f) ≫ pullback.snd f f =
      pullback.snd (𝟙 V) h ≫ h)
    (hγ : h ≫ f = (𝟙 W) ≫ w) :
    pullback.lift (pullback.fst (𝟙 V) h ≫ pullback.diagonal f)
        (pullback.snd (𝟙 V) h) hδ ≫
      ((pullbackLeftPullbackSndIso f f h).hom ≫ (pullback.congrHom rfl hw).inv) =
    pullback.snd (𝟙 V) h ≫ pullback.lift h (𝟙 W) hγ := by
  subst w
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.congrHom_inv, pullback.map_id,
      Category.comp_id,
      pullbackLeftPullbackSndIso_hom_fst, pullbackLeftPullbackSndIso_hom_snd,
      pullback.lift_fst_assoc,
      pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst]
  simpa only [Category.comp_id] using
    (pullback.condition (f := 𝟙 V) (g := h))

private theorem coefficient_comp_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
    (G : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (K : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (a : F ⟶ (g)_*[Ab.{u + 1}].obj G)
    (b : G ⟶ (f)_*[Ab.{u + 1}].obj K)
    (c : F ⟶ (f ≫ g)_*[Ab.{u + 1}].obj K)
    (hc : c = a ≫ (g)_*[Ab.{u + 1}].map b ≫
      (lowerStarComp Ab.{u + 1} f g).hom.app K) (U : Z.ProEt) :
    c.hom.app (op U) = a.hom.app (op U) ≫
      b.hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj U)) ≫
      K.obj.map ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) f g).hom.app U).op := by
  rw [hc]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app, lowerStarComp_hom_app_hom_app]

private theorem naturality_graph
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    (F : Cᵒᵖ ⥤ Ab.{u + 1}) (G : Dᵒᵖ ⥤ Ab.{u + 1})
    (η : F ⟶ H.op ⋙ G) {T P : C} {W R : D}
    (δ : T ⟶ P) (i : W ⟶ H.obj T) (γ : W ⟶ R)
    (c : R ⟶ H.obj P) (hc : γ ≫ c = i ≫ H.map δ) :
    η.app (op P) ≫ G.map c.op ≫ G.map γ.op =
      F.map δ.op ≫ η.app (op T) ≫ G.map i.op := by
  have hm := congrArg G.map (congrArg Quiver.Hom.op hc)
  simp only [op_comp, Functor.map_comp] at hm
  have hn := η.naturality δ.op
  change F.map δ.op ≫ η.app (op T) = η.app (op P) ≫ G.map (H.map δ).op at hn
  rw [hm, ← Category.assoc, ← hn, Category.assoc]

private theorem section_equation {A B C D E F G : Ab.{u + 1}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (γ : D ⟶ E)
    (δ : B ⟶ F) (h : F ⟶ G) (i : G ⟶ E) (w : A ⟶ D)
    (hw : w = a ≫ b ≫ c) (hn : b ≫ c ≫ γ = δ ≫ h ≫ i) (s : A) :
    γ (w s) = i (h (δ (a s))) := by
  have he := congrArg (fun k ↦ k (a s)) hn
  simpa only [hw, AddCommGrpCat.comp_apply] using he

set_option backward.isDefEq.respectTransparency false in
private theorem diagonal_graph_of_comp (B : Scheme.{u}) (V W : B.ProEt) (h : W ⟶ V)
    (F : Sheaf (Scheme.ProEt.topology B) Ab.{u + 1})
    (G : Sheaf (Scheme.ProEt.topology V.left) Ab.{u + 1})
    (K : Sheaf (Scheme.ProEt.topology W.left) Ab.{u + 1})
    (ηu : F ⟶ (V.hom)_*[Ab.{u + 1}].obj G)
    (ηh : G ⟶ (h.left)_*[Ab.{u + 1}].obj K)
    (ηw : F ⟶ (W.hom)_*[Ab.{u + 1}].obj K)
    (hc : ηw.hom.app (op V) = ηu.hom.app (op V) ≫
      ηh.hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ V.hom).obj V)) ≫
      K.obj.map ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) h.left V.hom W.hom
          (MorphismProperty.Over.w h).symm).hom.app V).op) :
    (∀ s : F.obj.obj (op V),
      K.obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift h.left (𝟙 W.left)
              (h.w.trans (Category.id_comp W.hom).symm))
            (pullback.lift_snd _ _ _) trivial :
              Scheme.ProEt.mk (𝟙 W.left) ⟶
                (MorphismProperty.Over.pullback @WeaklyEtale ⊤ W.hom).obj V).op
          (ηw.hom.app (op V) s) =
        K.obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift h.left (𝟙 W.left)
              ((Category.comp_id h.left).trans (Category.id_comp h.left).symm))
            (pullback.lift_snd _ _ _) trivial :
              Scheme.ProEt.mk (𝟙 W.left) ⟶
                (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h.left).obj
                  (Scheme.ProEt.mk (𝟙 V.left))).op
          (ηh.hom.app
            (op (Scheme.ProEt.mk (𝟙 V.left)))
            (G.obj.map
              (MorphismProperty.Over.homMk (pullback.diagonal V.hom)
                (pullback.diagonal_snd V.hom) trivial :
                  Scheme.ProEt.mk (𝟙 V.left) ⟶
                    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ V.hom).obj V).op
              (ηu.hom.app (op V) s)))) ∧
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h.left).map
        (MorphismProperty.Over.homMk (pullback.diagonal V.hom)
          (pullback.diagonal_snd V.hom) trivial :
            Scheme.ProEt.mk (𝟙 V.left) ⟶
              (MorphismProperty.Over.pullback @WeaklyEtale ⊤ V.hom).obj V)).left ≫
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
          h.left V.hom W.hom h.w.symm).inv.app V).left =
      pullback.snd (𝟙 V.left) h.left ≫
        pullback.lift h.left (𝟙 W.left)
          (h.w.trans (Category.id_comp W.hom).symm) := by
  have hw : h.left ≫ V.hom = W.hom := MorphismProperty.Over.w h
  let δ : Scheme.ProEt.mk (𝟙 V.left) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ V.hom).obj V :=
    MorphismProperty.Over.homMk (pullback.diagonal V.hom)
      (pullback.diagonal_snd V.hom) trivial
  let γ : Scheme.ProEt.mk (𝟙 W.left) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ W.hom).obj V :=
    MorphismProperty.Over.homMk
      (pullback.lift h.left (𝟙 W.left)
        (hw.trans (Category.id_comp W.hom).symm)) (pullback.lift_snd _ _ _) trivial
  let i : Scheme.ProEt.mk (𝟙 W.left) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h.left).obj
        (Scheme.ProEt.mk (𝟙 V.left)) :=
    MorphismProperty.Over.homMk
      (pullback.lift h.left (𝟙 W.left)
        ((Category.comp_id h.left).trans (Category.id_comp h.left).symm))
      (pullback.lift_snd _ _ _) trivial
  let H := MorphismProperty.Over.pullback @WeaklyEtale ⊤ h.left
  let c := MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
    h.left V.hom W.hom hw.symm
  have hgeom : H.map δ ≫ c.inv.app V =
      MorphismProperty.Over.homMk (pullback.snd (𝟙 V.left) h.left)
        (by exact Category.comp_id _) trivial ≫ γ := by
    apply MorphismProperty.Over.Hom.ext
    change
      pullback.lift
          (pullback.fst (𝟙 V.left) h.left ≫ pullback.diagonal V.hom)
          (pullback.snd (𝟙 V.left) h.left) _ ≫
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
          h.left V.hom W.hom hw.symm).inv.app V).left =
      pullback.snd (𝟙 V.left) h.left ≫
        pullback.lift h.left (𝟙 W.left) _
    change
      pullback.lift
          (pullback.fst (𝟙 V.left) h.left ≫ pullback.diagonal V.hom)
          (pullback.snd (𝟙 V.left) h.left) _ ≫
        ((pullbackLeftPullbackSndIso V.hom V.hom h.left).hom ≫
          (pullback.congrHom rfl hw.symm).inv) = _
    exact diagonal_graph_maps V.hom h.left W.hom hw.symm _ _
  have hgraph : γ ≫ c.hom.app V = i ≫ H.map δ := by
    apply (cancel_mono (c.inv.app V)).mp
    rw [Category.assoc, c.hom_inv_id_app, Category.comp_id,
      Category.assoc, hgeom, ← Category.assoc]
    have hi : i ≫ (MorphismProperty.Over.homMk
        (pullback.snd (𝟙 V.left) h.left) (by exact Category.comp_id _) trivial :
          H.obj (Scheme.ProEt.mk (𝟙 V.left)) ⟶ Scheme.ProEt.mk (𝟙 W.left)) =
        𝟙 (Scheme.ProEt.mk (𝟙 W.left)) := by
      apply MorphismProperty.Over.Hom.ext
      change pullback.lift h.left (𝟙 W.left) _ ≫
        pullback.snd (𝟙 V.left) h.left = 𝟙 W.left
      exact pullback.lift_snd _ _ _
    rw [hi, Category.id_comp]
  constructor
  · intro s
    change (K.obj.map γ.op)
        (ηw.hom.app (op V) s) =
      (K.obj.map i.op)
        (ηh.hom.app
          (op (Scheme.ProEt.mk (𝟙 V.left)))
          ((G.obj.map δ.op)
            (ηu.hom.app (op V) s)))
    have heq := naturality_graph H G.obj
      K.obj ηh.hom
      δ i γ (c.hom.app V) hgraph
    have he := section_equation
      (ηu.hom.app (op V))
      (ηh.hom.app
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ V.hom).obj V)))
      (K.obj.map (c.hom.app V).op)
      (K.obj.map γ.op)
      (G.obj.map δ.op)
      (ηh.hom.app
        (op (Scheme.ProEt.mk (𝟙 V.left))))
      (K.obj.map i.op)
      (ηw.hom.app (op V))
      (by convert hc using 1) (by convert heq using 1) s
    exact he
  · have he := congrArg (fun k ↦ k.left) hgeom
    simp only [MorphismProperty.Comma.comp_left] at he
    convert he using 1
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem diagonal_graph_family
    (F : (X : Scheme.{u}) → Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (η : {X Y : Scheme.{u}} → (f : X ⟶ Y) → F Y ⟶ (f)_*[Ab.{u + 1}].obj (F X))
    (hη : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      η (f ≫ g) = η g ≫ (g)_*[Ab.{u + 1}].map (η f) ≫
        (lowerStarComp Ab.{u + 1} f g).hom.app (F X))
    (B : Scheme.{u}) (V W : B.ProEt) (h : W ⟶ V) :
    (∀ s : (F B).obj.obj (op V),
      (F W.left).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift h.left (𝟙 W.left)
              (h.w.trans (Category.id_comp W.hom).symm))
            (pullback.lift_snd _ _ _) trivial :
              Scheme.ProEt.mk (𝟙 W.left) ⟶
                (MorphismProperty.Over.pullback @WeaklyEtale ⊤ W.hom).obj V).op
          ((η (X := (𝟭 Scheme).obj W.left)
              (Y := (Functor.fromPUnit B).obj W.right) W.hom).hom.app (op V) s) =
        (F W.left).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift h.left (𝟙 W.left)
              ((Category.comp_id h.left).trans (Category.id_comp h.left).symm))
            (pullback.lift_snd _ _ _) trivial :
              Scheme.ProEt.mk (𝟙 W.left) ⟶
                (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h.left).obj
                  (Scheme.ProEt.mk (𝟙 V.left))).op
          ((η (X := W.left) (Y := V.left) h.left).hom.app
            (op (Scheme.ProEt.mk (𝟙 V.left)))
            ((F V.left).obj.map
              (MorphismProperty.Over.homMk (pullback.diagonal V.hom)
                (pullback.diagonal_snd V.hom) trivial :
                  Scheme.ProEt.mk (𝟙 V.left) ⟶
                    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ V.hom).obj V).op
              ((η (X := (𝟭 Scheme).obj V.left)
                (Y := (Functor.fromPUnit B).obj V.right) V.hom).hom.app (op V) s)))) ∧
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h.left).map
        (MorphismProperty.Over.homMk (pullback.diagonal V.hom)
          (pullback.diagonal_snd V.hom) trivial :
            Scheme.ProEt.mk (𝟙 V.left) ⟶
              (MorphismProperty.Over.pullback @WeaklyEtale ⊤ V.hom).obj V)).left ≫
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
          h.left V.hom W.hom h.w.symm).inv.app V).left =
      pullback.snd (𝟙 V.left) h.left ≫
        pullback.lift h.left (𝟙 W.left)
          (h.w.trans (Category.id_comp W.hom).symm) := by
  have hc (w : W.left ⟶ B) (hw : w = h.left ≫ V.hom) :
      (η w).hom.app (op V) =
        (η V.hom).hom.app (op V) ≫
          (η h.left).hom.app
            (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ V.hom).obj V)) ≫
          (F W.left).obj.map
            ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
              h.left V.hom w hw).hom.app V).op := by
    subst w
    have he := coefficient_comp_app h.left V.hom
      (F B) (F V.left)
      (F W.left) (η V.hom)
      (η h.left)
      (η (h.left ≫ V.hom))
      (hη h.left V.hom) V
    convert he using 1
  have hh := hc W.hom (MorphismProperty.Over.w h).symm
  let ηu : F B ⟶
      (V.hom)_*[Ab.{u + 1}].obj (F V.left) :=
    η V.hom
  let ηh : F V.left ⟶
      (h.left)_*[Ab.{u + 1}].obj (F W.left) :=
    η h.left
  let ηw : F B ⟶
      (W.hom)_*[Ab.{u + 1}].obj (F W.left) :=
    η W.hom
  have he := @diagonal_graph_of_comp.{u} B V W h
    (F B) (F V.left)
    (F W.left) ηu ηh ηw
    (by convert hh using 1)
  dsimp only [ηu, ηh, ηw, Functor.fromPUnit, Functor.const] at he ⊢
  exact he

/-- Coefficient-mate composition evaluated along the diagonal and the graph. The
first conjunct is the section identity in `Λ_W(W/W)`; the second identifies the
base-changed diagonal with the graph under the very comparison used by `lowerStarComp`.
Here `u` and `w` are the structural maps of the test objects `V` and `W`, and `h.w`
is the equality `h.left ≫ V.hom = W.hom`. The restriction after `η_h` on the right
implements the canonical identification `V ×_V W ≅ W`.

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-prop-sfb-cartesian-coefficients/lem-sfb-eta-comp.proof.md`, composition identity
and final paragraph (blueprint: lem-sfb-coefficient-mate-diagonal-graph).

Proof plan:
1. Put P = V ×_B V (over V by its second projection), Q = P ×_V W and
   R = V ×_B W. The inverse component of `MorphismProperty.Over.pullbackComp`
   is e : Q ≅ R, sending (v1,v2,z) to (v1,z); its inverse inserts h(z).
   The pullback of the diagonal has domain D = V ×_V W, identified with W by
   its second projection. Its composite with e is gamma after this projection,
   since both maps have projections (h(z),z). This proves the second conjunct.
2. Apply `condensedPushforwardHom_comp` (`lem-sfb-eta-comp`) to h and u,
   evaluate at V and s, and use `def-sfb-finite-lower-star-comp` to express the
   comparison as restriction along e inverse. Thus η_w(s) = Λ_W(e inverse)(t),
   where t = η_{h,P}(η_{u,V}(s)).
3. Naturality of `condensedPushforwardHom Λ h.left` (`def-sfb-eta`) at the
   diagonal says restriction of t along its base change is η_{h,V} applied to
   diagonal restriction of η_{u,V}(s). Pushforward is restriction along base
   change (`def-sfb-finite-lower-star`), so this is the displayed right side.
4. Restrict step 2 along gamma. Contravariant functoriality and the geometric
   equality in step 1 identify the result with step 3. No monomorphism or
   constant-section assumption enters any of these steps. -/
theorem coefficientMate_diagonal_graph
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (B : Scheme.{u}) (V W : B.ProEt) (h : W ⟶ V) :
    (∀ s : (condensedRingObj Λ.X B).obj.obj (op V),
      (condensedRingObj Λ.X W.left).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift h.left (𝟙 W.left)
              (h.w.trans (Category.id_comp W.hom).symm))
            (pullback.lift_snd _ _ _) trivial :
              Scheme.ProEt.mk (𝟙 W.left) ⟶
                (MorphismProperty.Over.pullback @WeaklyEtale ⊤ W.hom).obj V).op
          ((condensedPushforwardHom Λ.X W.hom).hom.app (op V) s) =
        (condensedRingObj Λ.X W.left).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift h.left (𝟙 W.left)
              ((Category.comp_id h.left).trans (Category.id_comp h.left).symm))
            (pullback.lift_snd _ _ _) trivial :
              Scheme.ProEt.mk (𝟙 W.left) ⟶
                (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h.left).obj
                  (Scheme.ProEt.mk (𝟙 V.left))).op
          ((condensedPushforwardHom Λ.X h.left).hom.app
            (op (Scheme.ProEt.mk (𝟙 V.left)))
            ((condensedRingObj Λ.X V.left).obj.map
              (MorphismProperty.Over.homMk (pullback.diagonal V.hom)
                (pullback.diagonal_snd V.hom) trivial :
                  Scheme.ProEt.mk (𝟙 V.left) ⟶
                    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ V.hom).obj V).op
              ((condensedPushforwardHom Λ.X V.hom).hom.app (op V) s)))) ∧
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h.left).map
        (MorphismProperty.Over.homMk (pullback.diagonal V.hom)
          (pullback.diagonal_snd V.hom) trivial :
            Scheme.ProEt.mk (𝟙 V.left) ⟶
              (MorphismProperty.Over.pullback @WeaklyEtale ⊤ V.hom).obj V)).left ≫
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
          h.left V.hom W.hom h.w.symm).inv.app V).left =
      pullback.snd (𝟙 V.left) h.left ≫
        pullback.lift h.left (𝟙 W.left)
          (h.w.trans (Category.id_comp W.hom).symm) := by
  have he := diagonal_graph_family (@condensedRingObj.{u} Λ.X)
    (@condensedPushforwardHom.{u} Λ.X)
    (fun f g ↦ condensedPushforwardHom_comp Λ.X f g) B V W h
  exact he

end AlgebraicGeometry.ProEtale
