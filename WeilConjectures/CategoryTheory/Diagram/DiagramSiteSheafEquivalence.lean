/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Diagram.DiagramSiteTopology
public import Mathlib.CategoryTheory.Adjunction.Evaluation

/-! The sheaf part of the product-site realization.

Source: Stacks Project, Sites, Tags 00Z4, 00Z8 and 00XA (blueprint:
lem-weil-pbc-diagram-site-sheaf-equivalence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
def diagramSiteCurry {J C : Type u} [SmallCategory J] [SmallCategory C]
    (P : (Jᵒᵖ × C)ᵒᵖ ⥤ Type u) : J ⥤ Cᵒᵖ ⥤ Type u where
  obj j := (Prod.sectR (op j) C).op ⋙ P
  map {j k} a :=
    { app U := P.map (Prod.mkHom a.op (𝟙 U.unop)).op
      naturality := by
        intro U V f
        dsimp
        rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp]
        congr 2
        ext <;> simp }
  map_id j := by
    apply NatTrans.ext
    funext U
    dsimp
    change P.map (𝟙 (op (op j, U.unop))) = 𝟙 _
    exact P.map_id _
  map_comp a b := by
    apply NatTrans.ext
    funext U
    dsimp
    rw [← P.map_comp, ← op_comp]
    congr 2
    ext <;> simp

set_option backward.isDefEq.respectTransparency false in
def diagramSiteUncurry {J C : Type u} [SmallCategory J] [SmallCategory C]
    (P : J ⥤ Cᵒᵖ ⥤ Type u) : (Jᵒᵖ × C)ᵒᵖ ⥤ Type u where
  obj X := (P.obj X.unop.1.unop).obj (op X.unop.2)
  map {X Y} f := (P.map f.unop.1.unop).app (op X.unop.2) ≫
    (P.obj Y.unop.1.unop).map f.unop.2.op
  map_id X := by simp
  map_comp {X Y Z} f g := by
    dsimp
    simp only [P.map_comp, NatTrans.comp_app, Functor.map_comp, Category.assoc]
    rw [← NatTrans.naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of product sheaves to diagrams of vertical sheaves. -/
def diagramSiteSheafCurry (J C : Type u) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) :
    Sheaf (diagramSiteTopology J C K) (Type u) ⥤ J ⥤ Sheaf K (Type u) where
  obj F :=
    { obj j := ⟨_, (diagramSite_isSheaf_iff J C K F.obj).1 F.property (op j)⟩
      map a := ObjectProperty.homMk ((diagramSiteCurry F.obj).map a)
      map_id j := by
        apply Sheaf.hom_ext
        exact (diagramSiteCurry F.obj).map_id j
      map_comp a b := by
        apply Sheaf.hom_ext
        exact (diagramSiteCurry F.obj).map_comp a b }
  map f :=
    { app j := ObjectProperty.homMk (Functor.whiskerLeft (Prod.sectR (op j) C).op f.hom)
      naturality := by
        intro j k a
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext U
        exact f.hom.naturality (Prod.mkHom a.op (𝟙 U.unop)).op }

set_option backward.isDefEq.respectTransparency false in
/-- Assembly of a diagram of sheaves to a product sheaf. -/
def diagramSiteSheafUncurry (J C : Type u) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) :
    (J ⥤ Sheaf K (Type u)) ⥤ Sheaf (diagramSiteTopology J C K) (Type u) where
  obj F :=
    { obj := diagramSiteUncurry (F ⋙ sheafToPresheaf K (Type u))
      property := by
        apply (diagramSite_isSheaf_iff J C K _).2
        intro j
        let e : (Prod.sectR j C).op ⋙
            diagramSiteUncurry (F ⋙ sheafToPresheaf K (Type u)) ≅
            (F.obj j.unop).obj :=
          NatIso.ofComponents (fun U ↦ Iso.refl _) (by
            intro U V f
            simp [diagramSiteUncurry, Prod.sectR])
        exact (Presheaf.isSheaf_of_iso_iff e).2 (F.obj j.unop).property }
  map {F G} f := ObjectProperty.homMk
    { app X := (f.app X.unop.1.unop).hom.app (op X.unop.2)
      naturality := by
        intro X Y a
        dsimp [diagramSiteUncurry, Prod.sectR]
        rw [Category.assoc, (f.app Y.unop.1.unop).hom.naturality,
          ← Category.assoc]
        have H := congrArg (fun t ↦ t.hom.app (op X.unop.2))
          (f.naturality a.unop.1.unop)
        change ((F.map a.unop.1.unop).hom.app (op X.unop.2) ≫
          (f.app Y.unop.1.unop).hom.app (op X.unop.2)) = _ at H
        rw [H]
        exact Category.assoc _ _ _ }

set_option backward.isDefEq.respectTransparency false in
/-- The concrete equivalence between product sheaves and diagrams of sheaves. -/
def diagramSiteSheafEquivalence (J C : Type u) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) :
    Sheaf (diagramSiteTopology J C K) (Type u) ≌ (J ⥤ Sheaf K (Type u)) where
  functor := diagramSiteSheafCurry J C K
  inverse := diagramSiteSheafUncurry J C K
  unitIso := NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      dsimp [diagramSiteSheafCurry, diagramSiteSheafUncurry,
        diagramSiteCurry, diagramSiteUncurry, Prod.sectR]
      rw [Category.comp_id, Category.id_comp, ← F.obj.map_comp, ← op_comp]
      congr 2
      apply Quiver.Hom.unop_inj
      ext <;> simp))) (by
    intro F G f
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext X
    simp [diagramSiteSheafCurry, diagramSiteSheafUncurry, Prod.sectR])
  counitIso := NatIso.ofComponents (fun F ↦ NatIso.ofComponents
    (fun j ↦ ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦ Iso.refl _) (by
      intro U V f
      simp [diagramSiteSheafCurry, diagramSiteSheafUncurry,
        diagramSiteCurry, diagramSiteUncurry, Prod.sectR]))) (by
      intro j k a
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      simp [diagramSiteSheafCurry, diagramSiteSheafUncurry,
        diagramSiteCurry, diagramSiteUncurry, Prod.sectR])) (by
    intro F G f
    apply NatTrans.ext
    funext j
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    simp [diagramSiteSheafCurry, diagramSiteSheafUncurry, Prod.sectR])

  functor_unitIso_comp F := by
    ext j U x
    rfl

/-- Sheaves on the vertical product site are diagrams of component sheaves.

The proof factors product presheaf restrictions into the two coordinates, then
extends and glues matching families on vertical covering sieves. The resulting
inverse constructions are normalized on objects and morphisms. The evaluation
adjunction is the product right adjoint, transported across the equivalence; the
component evaluation preserves finite limits.

Source: Stacks Project, explicit product-site construction
(blueprint: lem-weil-pbc-diagram-site-sheaf-equivalence). -/
theorem exists_diagramSite_sheaf_equivalence
    (J C : Type u) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (T : GrothendieckTopology (Jᵒᵖ × C))
    (hT : ∀ (j : J) (U : C) (S : Sieve (op j, U)),
      S ∈ T (op j, U) ↔ S.functorPullback (Prod.sectR (op j) C) ∈ K U) :
    ∃ (E : Sheaf T (Type u) ≌ (J ⥤ Sheaf K (Type u))),
      (∀ (F : Sheaf T (Type u)) (j : J),
        ((E.functor.obj F).obj j).obj = (Prod.sectR (op j) C).op ⋙ F.obj) ∧
      (∀ (F : Sheaf T (Type u)) (j k : J) (a : j ⟶ k) (U : C),
        HEq (((E.functor.obj F).map a).hom.app (op U))
          (F.obj.map (Prod.mkHom a.op (𝟙 U)).op)) ∧
      (∀ (F G : Sheaf T (Type u)) (f : F ⟶ G) (j : J) (U : C),
        HEq (((E.functor.map f).app j).hom.app (op U))
          (f.hom.app (op (op j, U)))) ∧
      (∀ j : J,
        Nonempty (E.functor ⋙ (evaluation J (Sheaf K (Type u))).obj j ⊣
          evaluationRightAdjoint (Sheaf K (Type u)) j ⋙ E.inverse) ∧
        PreservesFiniteLimits
          (E.functor ⋙ (evaluation J (Sheaf K (Type u))).obj j)) := by
  have ht : T = diagramSiteTopology J C K := by
    apply GrothendieckTopology.ext
    funext X
    apply Set.ext
    intro S
    exact hT X.1.unop X.2 S
  subst T
  refine ⟨diagramSiteSheafEquivalence J C K, fun _ _ ↦ rfl,
    fun _ _ _ _ _ ↦ HEq.rfl, fun _ _ _ _ _ ↦ HEq.rfl, ?_⟩
  intro j
  refine ⟨⟨(diagramSiteSheafEquivalence J C K).toAdjunction.comp
    (evaluationAdjunctionLeft (Sheaf K (Type u)) j)⟩, inferInstance⟩

end CategoryTheory
