/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.AlgebraicGeometry.EtaleSetTerminalTransport
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory

/-! # Transport of matching families to fpqc descent data

Source: Stacks Project, Tag 0GLZ, first paragraph; Tag 09XN.
-/

@[expose] public section


universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 0GLZ, first proof paragraph; Sites, Tags 03CB and 03CC.
(blueprint: lem-cbc-comparison-matching-transport).
Proof: define t_i by the displayed formula. The inverse of the terminal second
projection is the canonical lift from the identity object. Expanding terminal
transport therefore identifies t_i with the inverse composition isomorphism applied
to e_i(s_i). On the overlap Z_i times_Y Z_j, apply the matching equation for s to
the two projections. Apply the restriction equation hres to both sides. The unit
compatibility of inverse-image composition and its associativity identify the two
results with the displayed fpqc compatibility equation. The equality of the two
maps to Y is pullback.condition; its transport is exactly Eq.mp in that equation.
This argument needs no covering assumption, including for an empty index type. -/
theorem proEtaleComparisonMatchingTransport
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (P : X.ProEtᵒᵖ ⥤ Type (u + 1))
    (e : ∀ Y : X.ProEt, P.obj (op Y) ≃
      ((Scheme.etaleSetPullback Y.hom).obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 Y.left))))
    (hres : ∀ (Y Z : X.ProEt) (g : Z ⟶ Y) (s : P.obj (op Y)),
      e Z (P.map g.op s) =
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ g.left) (Type (u + 1))
          (Y.left.smallGrothendieckTopology @Etale)
          (Z.left.smallGrothendieckTopology @Etale)).unit.app
            ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
              (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
          (etaleSetTerminalTransport Y.hom g.left Z.hom g.w F).inv) (e Y s))
    {I : Type v} (Y : X.ProEt) (Z : I → X.ProEt) (g : ∀ i, Z i ⟶ Y)
    (s : ∀ i, P.obj (op (Z i))) (hs : Presieve.Arrows.Compatible P g s) :
    ∃ t : ∀ i, ((Scheme.etaleSetPullback (g i).left).obj
        ((Scheme.etaleSetPullback Y.hom).obj F)).obj.obj
          (op (Scheme.Etale.mk (𝟙 (Z i).left))),
      (∀ i, t i =
        ((Scheme.etaleSetPullback (g i).left).obj
          ((Scheme.etaleSetPullback Y.hom).obj F)).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift (g i).left (𝟙 (Z i).left)
              ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp) :
            Scheme.Etale.mk (𝟙 (Z i).left) ⟶
              (MorphismProperty.Over.pullback @Etale ⊤ (g i).left).obj
                (Scheme.Etale.mk (𝟙 Y.left))).op
          ((etaleSetTerminalTransport Y.hom (g i).left (Z i).hom
            (MorphismProperty.Over.w (g i)) F).hom (e (Z i) (s i)))) ∧
      (∀ i j,
      ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
          Y.left ((Z i).left) (pullback ((g i).left) ((g j).left)) ((g i).left) (pullback.fst ((g
            i).left) ((g j).left))).hom.app ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
        (op (Scheme.Etale.mk (𝟙 (pullback ((g i).left) ((g j).left)))))
        (((Scheme.etaleSetPullback (pullback.fst ((g i).left) ((g j).left))).obj
            ((Scheme.etaleSetPullback ((g i).left)).obj ((Scheme.etaleSetPullback Y.hom).obj
              F))).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift (pullback.fst ((g i).left) ((g j).left)) (𝟙 (pullback ((g i).left) ((g
              j).left)))
              ((Category.comp_id _).trans (Category.id_comp _).symm))
            (by simp) :
            Scheme.Etale.mk (𝟙 (pullback ((g i).left) ((g j).left))) ⟶
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst ((g i).left) ((g j).left))).obj
                (Scheme.Etale.mk (𝟙 ((Z i).left)))).op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst ((g i).left) ((g j).left))) _
            (((Z i).left).smallGrothendieckTopology @Etale)
            ((pullback ((g i).left) ((g j).left)).smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback ((g i).left)).obj ((Scheme.etaleSetPullback Y.hom).obj
                F))).hom.app
            (op (Scheme.Etale.mk (𝟙 ((Z i).left)))) (t i))) =
        Eq.mp (congrArg (fun k : pullback ((g i).left) ((g j).left) ⟶ Y.left ↦
          ((Scheme.etaleSetPullback k).obj ((Scheme.etaleSetPullback Y.hom).obj F)).obj.obj
            (op (Scheme.Etale.mk (𝟙 (pullback ((g i).left) ((g j).left))))))
          (pullback.condition (f := (g i).left) (g := (g j).left)).symm)
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
            Y.left ((Z j).left) (pullback ((g i).left) ((g j).left)) ((g j).left) (pullback.snd
              ((g i).left) ((g j).left))).hom.app ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
          (op (Scheme.Etale.mk (𝟙 (pullback ((g i).left) ((g j).left)))))
          (((Scheme.etaleSetPullback (pullback.snd ((g i).left) ((g j).left))).obj
              ((Scheme.etaleSetPullback ((g j).left)).obj ((Scheme.etaleSetPullback Y.hom).obj
                F))).obj.map
            (MorphismProperty.Over.homMk
              (pullback.lift (pullback.snd ((g i).left) ((g j).left)) (𝟙 (pullback ((g i).left)
                ((g j).left)))
                ((Category.comp_id _).trans (Category.id_comp _).symm))
              (by simp) :
              Scheme.Etale.mk (𝟙 (pullback ((g i).left) ((g j).left))) ⟶
                (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd ((g i).left) ((g
                  j).left))).obj
                  (Scheme.Etale.mk (𝟙 ((Z j).left)))).op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd ((g i).left) ((g j).left))) _
              (((Z j).left).smallGrothendieckTopology @Etale)
              ((pullback ((g i).left) ((g j).left)).smallGrothendieckTopology @Etale)).unit.app
                ((Scheme.etaleSetPullback ((g j).left)).obj ((Scheme.etaleSetPullback Y.hom).obj
                  F))).hom.app
              (op (Scheme.Etale.mk (𝟙 ((Z j).left)))) (t j))))) := by
  sorry

end AlgebraicGeometry
