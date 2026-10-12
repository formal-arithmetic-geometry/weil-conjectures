/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Propagation of matching global sections to an arbitrary cone
Source: Stacks Project, Tag 09XN, paragraph beginning "Let V";
Sites Tags 03CB and 03CC.
(blueprint: lem-weil-pbc-etale-fpqc-matching-sections-pullback). -/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 09XN, paragraph beginning "Let V";
Sites Tags 03CB and 03CC for composition units.
(blueprint: lem-weil-pbc-etale-fpqc-matching-sections-pullback).

Proof: The equality a ≫ g_j = b ≫ g_k defines l = (a,b) from Z to
T_j ×_S T_k. Pull the given overlap equality back along l and restrict to the
identity étale object of Z. The unit is natural in the sheaf morphisms given by
the composition isomorphisms and in the site morphisms given by the terminal
restriction maps. Their associativity equation identifies the two successive
composition maps with composition along l ≫ pr_j and l ≫ pr_k. The composition
unit equation combines the two unit maps, and the presheaf functor law combines
the restrictions. The resulting maps to the fibre products have first projections
a and b and second projection id_Z, hence equal the displayed maps by pullback
uniqueness. The equations l ≫ pr_j = a and l ≫ pr_k = b identify the results with
the stated expressions; equality elimination gives precisely the transport along
hab. No covering, open, or representative is used. Empty Z gives the unique
sections; the same formulas hold when j = k or a and b are identities. -/
theorem etaleFpqcMatchingSections_pullback
    {S : Scheme.{u}} {I : Type v} (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (s : ∀ i, ((Scheme.etaleSetPullback (g i)).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 (T i)))))
    (hcompat : ∀ i j,
      ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
          S (T i) (pullback (g i) (g j)) (g i) (pullback.fst (g i) (g j))).hom.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 (pullback (g i) (g j)))))
        (((Scheme.etaleSetPullback (pullback.fst (g i) (g j))).obj
            ((Scheme.etaleSetPullback (g i)).obj F)).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift (pullback.fst (g i) (g j)) (𝟙 (pullback (g i) (g j)))
              ((Category.comp_id _).trans (Category.id_comp _).symm))
            (by simp) :
            Scheme.Etale.mk (𝟙 (pullback (g i) (g j))) ⟶
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst (g i) (g j))).obj
                (Scheme.Etale.mk (𝟙 (T i)))).op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst (g i) (g j))) _
            ((T i).smallGrothendieckTopology @Etale)
            ((pullback (g i) (g j)).smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback (g i)).obj F)).hom.app
            (op (Scheme.Etale.mk (𝟙 (T i)))) (s i))) =
        Eq.mp (congrArg (fun k : pullback (g i) (g j) ⟶ S ↦
          ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op (Scheme.Etale.mk (𝟙 (pullback (g i) (g j))))))
          (pullback.condition (f := g i) (g := g j)).symm)
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
            S (T j) (pullback (g i) (g j)) (g j) (pullback.snd (g i) (g j))).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 (pullback (g i) (g j)))))
          (((Scheme.etaleSetPullback (pullback.snd (g i) (g j))).obj
              ((Scheme.etaleSetPullback (g j)).obj F)).obj.map
            (MorphismProperty.Over.homMk
              (pullback.lift (pullback.snd (g i) (g j)) (𝟙 (pullback (g i) (g j)))
                ((Category.comp_id _).trans (Category.id_comp _).symm))
              (by simp) :
              Scheme.Etale.mk (𝟙 (pullback (g i) (g j))) ⟶
                (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd (g i) (g j))).obj
                  (Scheme.Etale.mk (𝟙 (T j)))).op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd (g i) (g j))) _
              ((T j).smallGrothendieckTopology @Etale)
              ((pullback (g i) (g j)).smallGrothendieckTopology @Etale)).unit.app
                ((Scheme.etaleSetPullback (g j)).obj F)).hom.app
              (op (Scheme.Etale.mk (𝟙 (T j)))) (s j))))) :
    ∀ (j k : I) (Z : Scheme.{u}) (a : Z ⟶ T j) (b : Z ⟶ T k)
      (hab : a ≫ g j = b ≫ g k),
      let Ga := (Scheme.etaleSetPullback (g j)).obj F
      let Gb := (Scheme.etaleSetPullback (g k)).obj F
      let Oa := Scheme.Etale.mk (𝟙 (T j))
      let Ob := Scheme.Etale.mk (𝟙 (T k))
      let δa : Scheme.Etale.mk (𝟙 Z) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ a).obj Oa :=
        MorphismProperty.Over.homMk
          (pullback.lift a (𝟙 Z) ((Category.comp_id _).trans (Category.id_comp _).symm))
          (by simp)
      let δb : Scheme.Etale.mk (𝟙 Z) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ b).obj Ob :=
        MorphismProperty.Over.homMk
          (pullback.lift b (𝟙 Z) ((Category.comp_id _).trans (Category.id_comp _).symm))
          (by simp)
      let ηa := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ a) (Type (u + 1))
        ((T j).smallGrothendieckTopology @Etale)
        (Z.smallGrothendieckTopology @Etale)).unit.app Ga).hom.app (op Oa)
      let ηb := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ b) (Type (u + 1))
        ((T k).smallGrothendieckTopology @Etale)
        (Z.smallGrothendieckTopology @Etale)).unit.app Gb).hom.app (op Ob)
      let ca := ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
        S (T j) Z (g j) a).hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 Z)))
      let cb := ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
        S (T k) Z (g k) b).hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 Z)))
      ca (((Scheme.etaleSetPullback a).obj Ga).obj.map δa.op (ηa (s j))) =
        Eq.mp (congrArg (fun f : Z ⟶ S ↦ ((Scheme.etaleSetPullback f).obj F).obj.obj
          (op (Scheme.Etale.mk (𝟙 Z)))) hab.symm)
          (cb (((Scheme.etaleSetPullback b).obj Gb).obj.map δb.op (ηb (s k)))) := by sorry

end AlgebraicGeometry
