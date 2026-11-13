/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenArbitraryCriterion
import WeilConjectures.AlgebraicGeometry.EtaleFpqcAgreementSectionsOverlap

/-! # Compatibility of agreement opens for a matching family

## References

* Stacks Project, Tag 09XN
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The agreement opens of the pulled-back sections along an fpqc family are compatible with the
pullbacks to the overlaps (Stacks, Tags 09XN, 09XM, 03CB and 03CC). -/
theorem etaleFpqcAgreementOpens_compatible
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
              (op (Scheme.Etale.mk (𝟙 (T j)))) (s j)))))
    (V : S.Etale) (t : F.obj.obj (op V))
    (E : ∀ j, (pullback V.hom (g j)).Opens)
    (hE : ∀ j (A : (T j).Etale)
      (m : A ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (g j)).obj V),
      Set.range m.left ⊆ (E j : Set (pullback V.hom (g j) : Scheme.{u})) ↔
        ((Scheme.etaleSetPullback (g j)).obj F).obj.map m.op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ (g j)) (Type (u + 1))
            (S.smallGrothendieckTopology @Etale)
            ((T j).smallGrothendieckTopology @Etale)).unit.app F).hom.app (op V) t) =
        ((Scheme.etaleSetPullback (g j)).obj F).obj.map
          (m ≫ MorphismProperty.Over.homMk
            (pullback.snd V.hom (g j)) (Category.comp_id _) :
            A ⟶ Scheme.Etale.mk (𝟙 (T j))).op (s j)) :
    ∀ j k,
      (pullback.fst (pullback.fst V.hom (g j)) (pullback.fst V.hom (g k))) ⁻¹ᵁ E j =
        (pullback.snd (pullback.fst V.hom (g j)) (pullback.fst V.hom (g k))) ⁻¹ᵁ E k := by
  classical
  let Q (j : I) := (MorphismProperty.Over.pullback @Etale ⊤ (g j)).obj V
  let G (j : I) := (Scheme.etaleSetPullback (g j)).obj F
  let x (j : I) := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ (g j)) (Type (u + 1))
    (S.smallGrothendieckTopology @Etale)
    ((T j).smallGrothendieckTopology @Etale)).unit.app F).hom.app (op V) t
  let y (j : I) := (G j).obj.map
    (MorphismProperty.Over.homMk (pullback.snd V.hom (g j)) (Category.comp_id _) :
      Q j ⟶ Scheme.Etale.mk (𝟙 (T j))).op (s j)
  have htest (j : I) (A : (T j).Etale) (m : A ⟶ Q j) :
      Set.range m.left ⊆ (E j : Set (pullback V.hom (g j) : Scheme.{u})) ↔
        (G j).obj.map m.op (x j) = (G j).obj.map m.op (y j) := by
    simpa only [y, op_comp, Functor.map_comp, comp_apply] using hE j A m
  intro j k
  let D := pullback (pullback.fst V.hom (g j)) (pullback.fst V.hom (g k))
  let p : D ⟶ (Q j).left :=
    pullback.fst (pullback.fst V.hom (g j)) (pullback.fst V.hom (g k))
  let q : D ⟶ (Q k).left :=
    pullback.snd (pullback.fst V.hom (g j)) (pullback.fst V.hom (g k))
  have hall (Z : Scheme.{u}) (a : Z ⟶ D) :
      Set.range (a ≫ p) ⊆ (E j : Set (pullback V.hom (g j) : Scheme.{u})) ↔
        Set.range (a ≫ q) ⊆ (E k : Set (pullback V.hom (g k) : Scheme.{u})) :=
    (etaleSections_equal_open_arbitrary_criterion (T j) (G j) (Q j)
      (x j) (y j) (E j) (htest j) Z (a ≫ p)).trans
      ((etaleFpqcAgreementSections_overlap_eq_iff T g F s hcompat V t j k Z a).trans
        (etaleSections_equal_open_arbitrary_criterion (T k) (G k) (Q k)
          (x k) (y k) (E k) (htest k) Z (a ≫ q)).symm)
  change p ⁻¹ᵁ E j = q ⁻¹ᵁ E k
  apply le_antisymm
  · let U := p ⁻¹ᵁ E j
    have hU : Set.range (U.ι ≫ p) ⊆ (E j : Set (pullback V.hom (g j) : Scheme.{u})) := by
      rintro z ⟨w, rfl⟩
      exact w.property
    have hW := (hall U.toScheme U.ι).mp hU
    intro z hz
    exact hW ⟨⟨z, hz⟩, rfl⟩
  · let U := q ⁻¹ᵁ E k
    have hU : Set.range (U.ι ≫ q) ⊆ (E k : Set (pullback V.hom (g k) : Scheme.{u})) := by
      rintro z ⟨w, rfl⟩
      exact w.property
    have hW := (hall U.toScheme U.ι).mpr hU
    intro z hz
    exact hW ⟨⟨z, hz⟩, rfl⟩

end AlgebraicGeometry
