/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleFpqcLocalRepresentatives
import WeilConjectures.AlgebraicGeometry.EtaleFpqcUnitsJointlyInjective

/-! # Compatible local representatives for fpqc descent of étale sections

Source: Stacks Project, Tag 09XN, the agreement-open construction before final gluing. -/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Local sections of an étale sheaf along an fpqc cover form a matching family, before
applying the sheaf axiom (Stacks, Tags 09XN and 09XM). -/
theorem etaleFpqcSections_exists_matching_family
    {S : Scheme.{u}} {I : Type v} (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S)
    (hcover : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S)
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
    ∃ (R : Sieve (Scheme.Etale.mk (𝟙 S)))
      (x : R.arrows.FamilyOfElements F.obj),
      R ∈ S.smallEtaleTopology (Scheme.Etale.mk (𝟙 S)) ∧ x.Compatible ∧
      ∀ i,
        let β := MorphismProperty.Over.pullback @Etale ⊤ (g i)
        let H := (Scheme.etaleSetPullback (g i)).obj F
        let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          β (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
          ((T i).smallGrothendieckTopology @Etale)).unit.app F
        ∀ (V : S.Etale) (f : V ⟶ Scheme.Etale.mk (𝟙 S)) (hf : R f),
          η.hom.app (op V) (x f hf) =
            H.obj.map (MorphismProperty.Over.homMk (β.obj V).hom
              (Category.comp_id _) : β.obj V ⟶ Scheme.Etale.mk (𝟙 (T i))).op (s i) := by
  classical
  let M (V : S.Etale) (t : F.obj.obj (op V)) : Prop := ∀ i,
    let β := MorphismProperty.Over.pullback @Etale ⊤ (g i)
    let H := (Scheme.etaleSetPullback (g i)).obj F
    let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      β (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
      ((T i).smallGrothendieckTopology @Etale)).unit.app F
    η.hom.app (op V) t =
      H.obj.map (MorphismProperty.Over.homMk (β.obj V).hom
        (Category.comp_id _) : β.obj V ⟶ Scheme.Etale.mk (𝟙 (T i))).op (s i)
  have hrestrict (V W : S.Etale) (a : W ⟶ V) (t : F.obj.obj (op V))
      (ht : M V t) : M W (F.obj.map a.op t) := by
    intro i
    let β := MorphismProperty.Over.pullback @Etale ⊤ (g i)
    let H := (Scheme.etaleSetPullback (g i)).obj F
    let pV : β.obj V ⟶ Scheme.Etale.mk (𝟙 (T i)) :=
      MorphismProperty.Over.homMk (β.obj V).hom (Category.comp_id _)
    let pW : β.obj W ⟶ Scheme.Etale.mk (𝟙 (T i)) :=
      MorphismProperty.Over.homMk (β.obj W).hom (Category.comp_id _)
    have hp : β.map a ≫ pV = pW := by
      apply MorphismProperty.Over.Hom.ext
      exact (β.map a).w
    dsimp only
    have hi := ht i
    dsimp only at hi
    rw [etaleSetInverseImageCompositionUnits.1 S (T i) (g i) F V W a t, hi]
    change H.obj.map (β.map a).op (H.obj.map pV.op (s i)) = H.obj.map pW.op (s i)
    rw [← CategoryTheory.comp_apply, ← H.obj.map_comp, ← op_comp, hp]
  obtain ⟨P, hP, hl⟩ := etaleFpqcSections_exists_local_representatives
    T g hcover F s hcompat
  let x : P.FamilyOfElements F.obj := fun V f hf ↦ Classical.choose (hl V f hf)
  have hx (V : S.Etale) (f : V ⟶ Scheme.Etale.mk (𝟙 S)) (hf : P f) :
      M V (x f hf) := Classical.choose_spec (hl V f hf)
  have hc : x.Compatible := by
    intro V W Z a b f f' hf hf' _
    apply etaleFpqcUnits_jointly_injective T g hcover F Z
    intro i
    exact (hrestrict V Z a (x f hf) (hx V f hf) i).trans
      (hrestrict W Z b (x f' hf') (hx W f' hf') i).symm
  refine ⟨Sieve.generate P, x.sieveExtend, hP, hc.sieveExtend, ?_⟩
  intro i
  dsimp only
  intro V f hf
  have h := hf.choose_spec
  exact hrestrict _ V h.choose _ (hx _ _ h.choose_spec.choose_spec.1) i

end AlgebraicGeometry
