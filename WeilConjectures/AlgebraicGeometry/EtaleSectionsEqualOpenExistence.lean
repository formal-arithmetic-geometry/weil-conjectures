/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.EtaleSubsheafFinalOpen
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualitySubterminal
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionsGeometricGermExt
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem global_sections_eq_of_germs (T : Scheme.{u})
    (G : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (p q : G.obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ T),
      (Scheme.pointSmallEtale y).toPresheafFiber (Scheme.Etale.mk (𝟙 T))
        (Over.homMk y (Category.comp_id y)) G.obj p =
      (Scheme.pointSmallEtale y).toPresheafFiber (Scheme.Etale.mk (𝟙 T))
        (Over.homMk y (Category.comp_id y)) G.obj q) : p = q := by
  apply etaleSetSection_ext_of_geometric_germs T G (Scheme.Etale.mk (𝟙 T))
  intro Ω _ _ y z
  have hz : z = Over.homMk y (Category.comp_id y) := by
    apply Over.OverMorphism.ext
    simpa using Over.w z
  rw [hz]
  exact h Ω y

/-- Source: Stacks Project, Étale Cohomology, Tag 09XM, existence argument.
There is an open on which the two sections agree with the stated universal property. -/
theorem exists_etaleSections_equal_open (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (V : S.Etale) (s t : F.obj.obj (op V)) :
    ∃ W : V.left.Opens, ∀ (T : Scheme.{u}) (a : T ⟶ V.left),
      (∃ b : T ⟶ W.toScheme, b ≫ W.ι = a) ↔
        ((Scheme.etaleSetPullback (a ≫ V.hom)).obj F).obj.map
          (MorphismProperty.Over.homMk
            (A := MorphismProperty.Over.mk ⊤ (𝟙 T) (inferInstance : Etale (𝟙 T)))
            (B := (MorphismProperty.Over.pullback @Etale ⊤ (a ≫ V.hom)).obj V)
            (pullback.lift a (𝟙 T) (Category.id_comp (a ≫ V.hom)).symm)
            (pullback.lift_snd a (𝟙 T) (Category.id_comp (a ≫ V.hom)).symm)).op
          (((@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
            (MorphismProperty.Over.pullback @Etale ⊤ (a ≫ V.hom)) (Type (u + 1)) _
            (S.smallGrothendieckTopology @Etale)
            (T.smallGrothendieckTopology @Etale)
            (Etale.isContinuous_overPullback (a ≫ V.hom)) _ _).unit.app F).hom.app (op V) s) =
        ((Scheme.etaleSetPullback (a ≫ V.hom)).obj F).obj.map
          (MorphismProperty.Over.homMk
            (A := MorphismProperty.Over.mk ⊤ (𝟙 T) (inferInstance : Etale (𝟙 T)))
            (B := (MorphismProperty.Over.pullback @Etale ⊤ (a ≫ V.hom)).obj V)
            (pullback.lift a (𝟙 T) (Category.id_comp (a ≫ V.hom)).symm)
            (pullback.lift_snd a (𝟙 T) (Category.id_comp (a ≫ V.hom)).symm)).op
          (((@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
            (MorphismProperty.Over.pullback @Etale ⊤ (a ≫ V.hom)) (Type (u + 1)) _
            (S.smallGrothendieckTopology @Etale)
            (T.smallGrothendieckTopology @Etale)
            (Etale.isContinuous_overPullback (a ≫ V.hom)) _ _).unit.app F).hom.app (op V) t) := by
  classical
  obtain ⟨H, hmono, hgerms⟩ := exists_etaleSections_equality_subterminal S F V s t
  have := hmono
  obtain ⟨W, hW, _⟩ := Scheme.existsUnique_open_of_etale_subsheaf_final.{u, u + 1} V.left H
  refine ⟨W, ?_⟩
  intro T a
  let G := (Scheme.etaleSetPullback (a ≫ V.hom)).obj F
  let I : T.Etale := Scheme.Etale.mk (𝟙 T)
  let k : I ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (a ≫ V.hom)).obj V :=
    MorphismProperty.Over.homMk
      (pullback.lift a (𝟙 T) (Category.id_comp (a ≫ V.hom)).symm)
      (pullback.lift_snd a (𝟙 T) (Category.id_comp (a ≫ V.hom)).symm)
  let η : F.obj.obj (op V) ⟶
      G.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ (a ≫ V.hom)).obj V)) :=
    ((@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
      (MorphismProperty.Over.pullback @Etale ⊤ (a ≫ V.hom)) (Type (u + 1)) _
      (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)
      (Etale.isContinuous_overPullback (a ≫ V.hom)) _ _).unit.app F).hom.app (op V)
  let r : F.obj.obj (op V) → G.obj.obj (op I) := fun z ↦ G.obj.map k.op (η z)
  change (∃ b : T ⟶ W.toScheme, b ≫ W.ι = a) ↔ r s = r t
  have hformula (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ T) :
      ((Scheme.pointSmallEtale y).toPresheafFiber I
        (Over.homMk y (Category.comp_id y)) G.obj (r s) =
       (Scheme.pointSmallEtale y).toPresheafFiber I
        (Over.homMk y (Category.comp_id y)) G.obj (r t)) ↔
      (Scheme.pointSmallEtale ((y ≫ a) ≫ V.hom)).toPresheafFiber V
        (Over.homMk (y ≫ a) rfl) F.obj s =
      (Scheme.pointSmallEtale ((y ≫ a) ≫ V.hom)).toPresheafFiber V
        (Over.homMk (y ≫ a) rfl) F.obj t := by
    obtain ⟨c, hc, hunit, _⟩ :=
      etaleSetInverseImageStalkGerm S T (a ≫ V.hom) F Ω y
    have hp : (Scheme.pointSmallEtale y).fiber.map k
        (Over.homMk y (Category.comp_id y)) =
        Over.homMk (pullback.lift (y ≫ a) y (Category.assoc y a V.hom))
          (pullback.lift_snd (y ≫ a) y (Category.assoc y a V.hom)) := by
      apply Over.OverMorphism.ext
      change y ≫ pullback.lift a (𝟙 T) _ = pullback.lift (y ≫ a) y _
      apply pullback.hom_ext <;> simp
    have heq (z : F.obj.obj (op V)) :
        c ((Scheme.pointSmallEtale y).toPresheafFiber I
          (Over.homMk y (Category.comp_id y)) G.obj (r z)) =
        (Scheme.pointSmallEtale (y ≫ (a ≫ V.hom))).toPresheafFiber V
          (Over.homMk (y ≫ a) (Category.assoc y a V.hom)) F.obj z := by
      have hn := ConcreteCategory.congr_hom
        ((Scheme.pointSmallEtale y).toPresheafFiber_w k
          (Over.homMk y (Category.comp_id y)) G.obj)
        (η z)
      simp only [types_comp_apply] at hn
      rw [hp] at hn
      rw [show (Scheme.pointSmallEtale y).toPresheafFiber I
          (Over.homMk y (Category.comp_id y)) G.obj (r z) = _ from hn]
      exact hunit V (Over.homMk (y ≫ a) (Category.assoc y a V.hom)) z
    rw [← hc.1.eq_iff, heq s, heq t]
    have htransport (e : Spec (.of Ω) ⟶ S) (he : (y ≫ a) ≫ V.hom = e) :
        ((Scheme.pointSmallEtale e).toPresheafFiber V (Over.homMk (y ≫ a) he) F.obj s =
         (Scheme.pointSmallEtale e).toPresheafFiber V (Over.homMk (y ≫ a) he) F.obj t) ↔
        ((Scheme.pointSmallEtale ((y ≫ a) ≫ V.hom)).toPresheafFiber V
          (Over.homMk (y ≫ a) rfl) F.obj s =
         (Scheme.pointSmallEtale ((y ≫ a) ≫ V.hom)).toPresheafFiber V
          (Over.homMk (y ≫ a) rfl) F.obj t) := by
      subst e
      rfl
    exact htransport _ (Category.assoc y a V.hom)
  constructor
  · rintro ⟨b, hb⟩
    apply global_sections_eq_of_germs T G
    intro Ω _ _ y
    apply (hformula Ω y).mpr
    apply (hgerms Ω (y ≫ a)).mp
    apply ((hW.2 Ω (y ≫ a)).1).mp
    simp only [← hb, Scheme.Hom.comp_apply]
    exact (Scheme.Opens.range_ι W).subset (Set.mem_range_self _)
  · intro h
    have hrange : Set.range a ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      have hy := (hformula _ (T.algClosurePoint z)).mp
        (congrArg ((Scheme.pointSmallEtale (T.algClosurePoint z)).toPresheafFiber I
          (Over.homMk (T.algClosurePoint z) (Category.comp_id _)) G.obj) h)
      have hw := ((hW.2 _ (T.algClosurePoint z ≫ a)).1).mpr
        ((hgerms _ (T.algClosurePoint z ≫ a)).mpr hy)
      simpa using hw
    exact ⟨IsOpenImmersion.lift W.ι a hrange, IsOpenImmersion.lift_fac W.ι a hrange⟩

end AlgebraicGeometry
