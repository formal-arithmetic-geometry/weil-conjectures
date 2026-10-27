/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientDiagramProjectionData
import all Sheaf.Paper.SemilinearDerivedSections
import Sheaf.Paper.QuotientReductionTensorEvaluation
import Sheaf.Paper.QuotientDiagramProjectionConstruction

/-! # Evaluation of the quotient-diagram projection mate

The presentation interface is re-exported from `QuotientDiagramProjectionData`.
The finite coefficient mate is computed by the normalized adjunction counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open WeilConjectures.SemilinearSections
namespace SheafOfModules.QuotientDiagramProjection
variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}
  {A : Type (max c v r)} [CommRing A] {I : Ideal A}
  {uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf K (Type (max c v r))}
  {uPush : Sheaf K (Type (max c v r)) ⥤ Sheaf J (Type (max c v r))}
  {adj : uInv ⊣ uPush} (p : Presentation.{c, v, r} J K A I uInv uPush adj)

private theorem projection_naturality
    {D E : Type*} [Category* D] [Category* E]
    (T : D × D ⥤ D) (S : E × E ⥤ E) {F : D ⥤ E} {G : E ⥤ D}
    (a : F ⊣ G) (μ : T ⋙ F ≅ (F.prod F) ⋙ S)
    {N N' : E} {P P' : D} (h : N ⟶ N') (k : P ⟶ P') :
    T.map (Prod.mkHom (G.map h) k) ≫
        a.homEquiv _ _ (μ.hom.app (G.obj N', P') ≫
          S.map (Prod.mkHom (a.counit.app N') (𝟙 _))) =
      a.homEquiv _ _ (μ.hom.app (G.obj N, P) ≫
          S.map (Prod.mkHom (a.counit.app N) (𝟙 _))) ≫
        G.map (S.map (Prod.mkHom h (F.map k))) := by
  apply (a.homEquiv _ _).symm.injective
  rw [a.homEquiv_naturality_left_symm, a.homEquiv_naturality_right_symm]
  simp only [Equiv.symm_apply_apply]
  have hn := μ.hom.naturality (Prod.mkHom (G.map h) k)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← S.map_comp]
  apply congrArg (fun f ↦ μ.hom.app (G.obj N, P) ≫ S.map f)
  apply Prod.ext
  · exact a.counit.naturality h
  · simp

attribute [local irreducible] HasDerivedCategory.standard DerivedCategory
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  CoefficientClosedStructure.tensor

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem coefficient_counit : ∀ (n : ℕ)
    (H : SemilinearSections.D.{c, v, max c v r} K (p.geometry.rings.obj (constant.{c, v, r} J A))),
    (SemilinearSections.derivedExact.{c, v, max c v r, c, v} J K (finite.{c, v, r} J A I n)
      (p.quotient.coefficients n)
        (p.quotient.inverseImage n).modules).map (finiteMate p n H) ≫
        (p.quotient.derivedLevelAdjunction n).counit.app ((p.x.levels n).T.obj H) =
      (finitePull p n ((p.geometry.right (constant.{c, v, r} J A)).obj H)).hom ≫
        (p.x.levels n).T.map
          ((p.geometry.adjunction (constant.{c, v, r} J A)).counit.app H) := by
  intro n H
  let V := SemilinearSections.derivedExact.{c, v, max c v r, c, v} J K
    (finite.{c, v, r} J A I n) (p.quotient.coefficients n)
    (p.quotient.inverseImage n).modules
  let E := SemilinearSections.e.{c, v, max c v r} J
    (finite.{c, v, r} J A I) (quotientTransition.{c, v, r} J A I) n
  let F := SemilinearSections.e.{c, v, max c v r} K p.quotient.coefficients
    p.quotient.coefficientTransition n
  simp only [finiteMate, Functor.map_comp, Category.assoc]
  have hc := (p.quotient.derivedLevelAdjunction n).counit.naturality
    ((p.x.evaluation n).hom.app H)
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  rw [hc]
  erw [reassoc_of% (p.quotient.counit_evaluation n (p.x.functor.obj H))]
  have hn := (p.quotient.pullEvaluation n).inv.naturality (coefficientMate p H)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← F.map_comp_assoc]
  have hm : p.quotient.pull.mapDerivedCategory.map (coefficientMate p H) ≫
      p.quotient.adjunction.counit.app (p.x.functor.obj H) =
      p.pull.hom.app ((p.geometry.right (constant.{c, v, r} J A)).obj H) ≫
        p.x.functor.map ((p.geometry.adjunction (constant.{c, v, r} J A)).counit.app H) := by
    exact (p.quotient.adjunction.homEquiv _ _).symm_apply_apply _
  rw [hm, F.map_comp]
  simp only [Category.assoc]
  have hx := (p.x.evaluation n).hom.naturality
    ((p.geometry.adjunction (constant.{c, v, r} J A)).counit.app H)
  dsimp only [Functor.comp_map] at hx
  erw [hx]
  simp only [finitePull, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem coefficientMate_naturality
    (H H' : SemilinearSections.D.{c, v, max c v r} K
      (p.geometry.rings.obj (constant.{c, v, r} J A))) (h : H ⟶ H') :
    p.y.functor.map ((p.geometry.right (constant.{c, v, r} J A)).map h) ≫
        coefficientMate p H' =
      coefficientMate p H ≫ p.quotient.push.rightDerivedFunctor.map (p.x.functor.map h) := by
  apply (p.quotient.adjunction.homEquiv _ _).symm.injective
  rw [p.quotient.adjunction.homEquiv_naturality_left_symm,
    p.quotient.adjunction.homEquiv_naturality_right_symm]
  simp only [coefficientMate, Equiv.symm_apply_apply]
  have hn := p.pull.hom.naturality ((p.geometry.right (constant.{c, v, r} J A)).map h)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← p.x.functor.map_comp]
  have hc := (p.geometry.adjunction (constant.{c, v, r} J A)).counit.naturality h
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  rw [hc, p.x.functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem tensorProjection_naturality
    (N N' : SemilinearSections.DS.{c, v, max c v r} K p.quotient.coefficients
      p.quotient.coefficientTransition)
    (P P' : SemilinearSections.DS.{c, v, max c v r} J (finite.{c, v, r} J A I)
      (quotientTransition.{c, v, r} J A I)) (h : N ⟶ N') (k : P ⟶ P') :
    p.source.closed.tensor.map
        (Prod.mkHom (p.quotient.push.rightDerivedFunctor.map h) k) ≫
      p.quotient.tensorProjection J (finite.{c, v, r} J A I)
        (quotientTransition.{c, v, r} J A I) p.source K uInv uPush adj N' P' =
    p.quotient.tensorProjection J (finite.{c, v, r} J A I)
        (quotientTransition.{c, v, r} J A I) p.source K uInv uPush adj N P ≫
      p.quotient.push.rightDerivedFunctor.map
        (p.quotient.target.closed.tensor.map
          (Prod.mkHom h (p.quotient.pull.mapDerivedCategory.map k))) := by
  exact projection_naturality p.source.closed.tensor p.quotient.target.closed.tensor
    p.quotient.adjunction p.quotient.tensorPullback h k

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem targetBalance_naturality
    (H H' : SemilinearSections.D.{c, v, max c v r} K
      (p.geometry.rings.obj (constant.{c, v, r} J A)))
    (L L' : SemilinearSections.D.{c, v, max c v r} J (constant.{c, v, r} J A))
    (h : H ⟶ H') (k : L ⟶ L') :
    p.quotient.target.closed.tensor.map
        (Prod.mkHom (p.x.functor.map h)
          (p.quotient.pull.mapDerivedCategory.map (p.y.functor.map k))) ≫
        (targetBalance p H' L').inv =
      (targetBalance p H L).inv ≫ p.x.functor.map
        (p.tensorX.ambient.tensor.map
          (Prod.mkHom h ((p.geometry.left (constant.{c, v, r} J A)).map k))) := by
  have hn := p.tensorX.balance.inv.naturality
    (Prod.mkHom h ((p.geometry.left (constant.{c, v, r} J A)).map k))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  dsimp only [targetBalance, Iso.trans_inv, Functor.mapIso_inv, Iso.prod_inv,
    Iso.refl_inv, Iso.symm_inv]
  rw [← Category.assoc, ← p.quotient.target.closed.tensor.map_comp]
  have hp := p.pull.hom.naturality k
  dsimp only [Functor.comp_map] at hp
  have hm : Prod.mkHom (p.x.functor.map h)
      (p.quotient.pull.mapDerivedCategory.map (p.y.functor.map k)) ≫
        Prod.mkHom (𝟙 _) (p.pull.hom.app L') =
      Prod.mkHom (𝟙 _) (p.pull.hom.app L) ≫
        Prod.mkHom (p.x.functor.map h)
          (p.x.functor.map ((p.geometry.left (constant.{c, v, r} J A)).map k)) := by
    apply Prod.ext
    · change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      simp
    · exact hp
  erw [hm, p.quotient.target.closed.tensor.map_comp, Category.assoc, hn]
  simp only [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem arrow_naturality : ∀
    (H H' : SemilinearSections.D.{c, v, max c v r} K (p.geometry.rings.obj (constant.{c, v, r} J
      A)))
    (L L' : SemilinearSections.D.{c, v, max c v r} J (constant.{c, v, r} J A)) (h : H ⟶ H') (k : L
      ⟶ L'),
    p.y.functor.map (p.tensorY.ambient.tensor.map
        (Prod.mkHom ((p.geometry.right (constant.{c, v, r} J A)).map h) k)) ≫
        arrow p H' L' =
      arrow p H L ≫ p.quotient.push.rightDerivedFunctor.map
        (p.x.functor.map (p.tensorX.ambient.tensor.map
          (Prod.mkHom h ((p.geometry.left (constant.{c, v, r} J A)).map k))))
 := by
  intro H H' L L' h k
  have hy := p.tensorY.balance.hom.naturality
    (Prod.mkHom ((p.geometry.right (constant.{c, v, r} J A)).map h) k)
  dsimp only [Functor.comp_map, Functor.prod_map] at hy
  dsimp only [arrow]
  rw [reassoc_of% hy]
  have hm :
      p.source.closed.tensor.map
          (Prod.mkHom (p.y.functor.map
            ((p.geometry.right (constant.{c, v, r} J A)).map h)) (p.y.functor.map k)) ≫
        p.source.closed.tensor.map (Prod.mkHom (coefficientMate p H') (𝟙 _)) =
      p.source.closed.tensor.map (Prod.mkHom (coefficientMate p H) (𝟙 _)) ≫
        p.source.closed.tensor.map
          (Prod.mkHom (p.quotient.push.rightDerivedFunctor.map (p.x.functor.map h))
            (p.y.functor.map k)) := by
    simp only [← p.source.closed.tensor.map_comp]
    congr 1
    ext
    · exact coefficientMate_naturality p H H' h
    · simp
  rw [reassoc_of% hm]
  rw [reassoc_of% (tensorProjection_naturality p _ _ _ _
    (p.x.functor.map h) (p.y.functor.map k))]
  rw [← p.quotient.push.rightDerivedFunctor.map_comp]
  rw [targetBalance_naturality p H H' L L' h k,
    p.quotient.push.rightDerivedFunctor.map_comp]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem targetBalance_evaluation (n : ℕ)
    (H : D.{c, v, max c v r} K (p.geometry.rings.obj (constant.{c, v, r} J A)))
    (L : D.{c, v, max c v r} J (constant.{c, v, r} J A)) :
    (e K p.quotient.coefficients p.quotient.coefficientTransition n).map
        (targetBalance p H L).inv ≫
      (p.x.evaluation n).hom.app (p.tensorX.ambient.tensor.obj
        (H, (p.geometry.left (constant.{c, v, r} J A)).obj L)) ≫
      (finiteTargetBalance p n H L).hom =
    ((p.quotient.target.tensorEvaluation n).hom.app
        (p.x.functor.obj H, p.quotient.pull.mapDerivedCategory.obj (p.y.functor.obj L)) ≫
      (p.quotient.target.levelClosed n).tensor.map
        (Prod.mkHom (𝟙 _) ((p.quotient.pullEvaluation n).hom.app (p.y.functor.obj L)))) ≫
      (p.quotient.target.levelClosed n).tensor.map
        (Prod.mkHom ((p.x.evaluation n).hom.app H)
          ((derivedExact J K (finite.{c, v, r} J A I n) (p.quotient.coefficients n)
            (p.quotient.inverseImage n).modules).map ((p.y.evaluation n).hom.app L))) := by
  let F := e K p.quotient.coefficients p.quotient.coefficientTransition n
  let t := (p.quotient.target.levelClosed n).tensor
  have hx := reductionTensorEvaluation p.x p.quotient.target p.tensorX n H
    ((p.geometry.left (constant.{c, v, r} J A)).obj L)
  have hx' : F.map (p.tensorX.balance.inv.app
        (H, (p.geometry.left (constant.{c, v, r} J A)).obj L)) ≫
      (p.x.evaluation n).hom.app (p.tensorX.ambient.tensor.obj
        (H, (p.geometry.left (constant.{c, v, r} J A)).obj L)) ≫
      (p.tensorX.finiteBalance n).hom.app
        (H, (p.geometry.left (constant.{c, v, r} J A)).obj L) =
    (p.quotient.target.tensorEvaluation n).hom.app
        (p.x.functor.obj H,
          p.x.functor.obj ((p.geometry.left (constant.{c, v, r} J A)).obj L)) ≫
      t.map (Prod.mkHom ((p.x.evaluation n).hom.app H)
        ((p.x.evaluation n).hom.app
          ((p.geometry.left (constant.{c, v, r} J A)).obj L))) := by
    apply (cancel_epi (F.map (p.tensorX.balance.hom.app
      (H, (p.geometry.left (constant.{c, v, r} J A)).obj L)))).1
    rw [← F.map_comp_assoc, Iso.hom_inv_id_app, F.map_id, Category.id_comp]
    exact hx.symm
  have hp : F.map (p.pull.hom.app L) ≫
      (p.x.evaluation n).hom.app
        ((p.geometry.left (constant.{c, v, r} J A)).obj L) ≫
      (finitePull p n L).inv =
    (p.quotient.pullEvaluation n).hom.app (p.y.functor.obj L) ≫
      (derivedExact J K (finite.{c, v, r} J A I n) (p.quotient.coefficients n)
        (p.quotient.inverseImage n).modules).map ((p.y.evaluation n).hom.app L) := by
    dsimp only [finitePull, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      Iso.app_hom, Iso.app_inv]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    erw [← F.map_comp_assoc, Iso.hom_inv_id_app, F.map_id, Category.id_comp]
  dsimp only [targetBalance, finiteTargetBalance, Iso.trans_inv, Iso.trans_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Iso.prod_inv, Iso.prod_hom, Iso.refl_inv,
    Iso.refl_hom, Iso.symm_inv, Iso.symm_hom]
  simp only [Functor.map_comp, Category.assoc, Iso.app_hom, Iso.app_inv]
  erw [reassoc_of% hx']
  have hn := (p.quotient.target.tensorEvaluation n).hom.naturality
    (Prod.mkHom (𝟙 (p.x.functor.obj H)) (p.pull.hom.app L))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  erw [reassoc_of% hn]
  erw [← t.map_comp, ← t.map_comp, ← t.map_comp]
  apply congrArg (fun f ↦ (p.quotient.target.tensorEvaluation n).hom.app
    (p.x.functor.obj H, p.quotient.pull.mapDerivedCategory.obj (p.y.functor.obj L)) ≫
      t.map f)
  apply Prod.ext
  · simp
  · dsimp only [prod_comp, Prod.mkHom]
    simpa only [Category.assoc, F.map_id, Category.id_comp] using hp

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem sourceBalance_evaluation (n : ℕ)
    (H : D.{c, v, max c v r} K (p.geometry.rings.obj (constant.{c, v, r} J A)))
    (L : D.{c, v, max c v r} J (constant.{c, v, r} J A)) :
    (e J (finite.{c, v, r} J A I) (quotientTransition.{c, v, r} J A I) n).map
        (p.tensorY.balance.hom.app
          ((p.geometry.right (constant.{c, v, r} J A)).obj H, L)) ≫
      (e J (finite.{c, v, r} J A I) (quotientTransition.{c, v, r} J A I) n).map
        (p.source.closed.tensor.map (Prod.mkHom (coefficientMate p H) (𝟙 _))) ≫
      (p.source.tensorEvaluation n).hom.app
        (p.quotient.push.rightDerivedFunctor.obj (p.x.functor.obj H), p.y.functor.obj L) ≫
      (p.source.levelClosed n).tensor.map
        (Prod.mkHom ((p.quotient.pushEvaluation n).hom.app (p.x.functor.obj H)) (𝟙 _)) ≫
      (p.source.levelClosed n).tensor.map
        (Prod.mkHom ((p.quotient.levelPush n).rightDerivedFunctor.map
          ((p.x.evaluation n).hom.app H)) ((p.y.evaluation n).hom.app L)) =
    (p.y.evaluation n).hom.app (p.tensorY.ambient.tensor.obj
      ((p.geometry.right (constant.{c, v, r} J A)).obj H, L)) ≫
      (p.tensorY.finiteBalance n).hom.app
        ((p.geometry.right (constant.{c, v, r} J A)).obj H, L) ≫
      (p.source.levelClosed n).tensor.map (Prod.mkHom (finiteMate p n H) (𝟙 _)) := by
  let t := (p.source.levelClosed n).tensor
  have hn := (p.source.tensorEvaluation n).hom.naturality
    (Prod.mkHom (coefficientMate p H) (𝟙 (p.y.functor.obj L)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [reassoc_of% hn]
  have hm : t.map (Prod.mkHom
        ((e J (finite.{c, v, r} J A I) (quotientTransition.{c, v, r} J A I) n).map
          (coefficientMate p H)) (𝟙 _)) ≫
      t.map (Prod.mkHom ((p.quotient.pushEvaluation n).hom.app (p.x.functor.obj H)) (𝟙 _)) ≫
      t.map (Prod.mkHom ((p.quotient.levelPush n).rightDerivedFunctor.map
        ((p.x.evaluation n).hom.app H)) ((p.y.evaluation n).hom.app L)) =
    t.map (Prod.mkHom ((p.y.evaluation n).hom.app
        ((p.geometry.right (constant.{c, v, r} J A)).obj H))
      ((p.y.evaluation n).hom.app L)) ≫
      t.map (Prod.mkHom (finiteMate p n H) (𝟙 _)) := by
    simp only [← t.map_comp]
    congr 1
    apply Prod.ext
    · dsimp only [prod_comp, Prod.mkHom]
      simp only [finiteMate, Iso.hom_inv_id_app_assoc]
    · simp
  erw [(e J (finite.{c, v, r} J A I)
    (quotientTransition.{c, v, r} J A I) n).map_id]
  erw [hm]
  rw [reassoc_of% (reductionTensorEvaluation p.y p.source p.tensorY n
    ((p.geometry.right (constant.{c, v, r} J A)).obj H) L)]

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem arrow_evaluation : ∀ (n : ℕ)
    (H : D.{c, v, max c v r} K (p.geometry.rings.obj (constant.{c, v, r} J A)))
    (L : D.{c, v, max c v r} J (constant.{c, v, r} J A)),
    (e J (finite.{c, v, r} J A I) (quotientTransition.{c, v, r} J A I) n).map
        (arrow p H L) ≫
      (p.quotient.pushEvaluation n).hom.app (p.x.functor.obj
        (p.tensorX.ambient.tensor.obj
          (H, (p.geometry.left (constant.{c, v, r} J A)).obj L))) ≫
      (p.quotient.levelPush n).rightDerivedFunctor.map
        ((p.x.evaluation n).hom.app (p.tensorX.ambient.tensor.obj
          (H, (p.geometry.left (constant.{c, v, r} J A)).obj L)) ≫
            (finiteTargetBalance p n H L).hom) =
    (p.y.evaluation n).hom.app (p.tensorY.ambient.tensor.obj
      ((p.geometry.right (constant.{c, v, r} J A)).obj H, L)) ≫
      (p.tensorY.finiteBalance n).hom.app
        ((p.geometry.right (constant.{c, v, r} J A)).obj H, L) ≫
      (p.source.levelClosed n).tensor.map (Prod.mkHom (finiteMate p n H) (𝟙 _)) ≫
      p.quotient.levelTensorProjection J (finite.{c, v, r} J A I)
        (quotientTransition.{c, v, r} J A I) p.source K uInv uPush adj n
        ((p.x.levels n).T.obj H) ((p.y.levels n).T.obj L) := by
  intro n H L
  let Rn := (p.quotient.levelPush n).rightDerivedFunctor
  have hn := (p.quotient.pushEvaluation n).hom.naturality (targetBalance p H L).inv
  dsimp only [Functor.comp_map] at hn
  dsimp only [arrow]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [← Rn.map_comp_assoc, ← Rn.map_comp]
  simp only [Category.assoc]
  rw [targetBalance_evaluation p n H L, Rn.map_comp]
  have hproj := WeilConjectures.SemilinearSections.projection_evaluation J
    (finite.{c, v, r} J A I) (quotientTransition.{c, v, r} J A I) p.source
    K uInv uPush adj p.quotient n (p.x.functor.obj H) (p.y.functor.obj L)
  rw [reassoc_of% hproj]
  have hlevel : (p.source.levelClosed n).tensor.map
      (Prod.mkHom (Rn.map ((p.x.evaluation n).hom.app H))
        ((p.y.evaluation n).hom.app L)) ≫
      p.quotient.levelTensorProjection J (finite.{c, v, r} J A I)
        (quotientTransition.{c, v, r} J A I) p.source K uInv uPush adj n
        ((p.x.levels n).T.obj H) ((p.y.levels n).T.obj L) =
    p.quotient.levelTensorProjection J (finite.{c, v, r} J A I)
        (quotientTransition.{c, v, r} J A I) p.source K uInv uPush adj n
        ((e K p.quotient.coefficients p.quotient.coefficientTransition n).obj
          (p.x.functor.obj H))
        ((e J (finite.{c, v, r} J A I) (quotientTransition.{c, v, r} J A I) n).obj
          (p.y.functor.obj L)) ≫
      Rn.map ((p.quotient.target.levelClosed n).tensor.map
        (Prod.mkHom ((p.x.evaluation n).hom.app H)
          ((derivedExact J K (finite.{c, v, r} J A I n) (p.quotient.coefficients n)
            (p.quotient.inverseImage n).modules).map ((p.y.evaluation n).hom.app L)))) :=
    projection_naturality (p.source.levelClosed n).tensor
      (p.quotient.target.levelClosed n).tensor (p.quotient.derivedLevelAdjunction n)
      (p.quotient.levelTensorPullback n) ((p.x.evaluation n).hom.app H)
      ((p.y.evaluation n).hom.app L)
  rw [← hlevel]
  exact (reassoc_of% (sourceBalance_evaluation p n H L)) _

/-- The quotient-diagram projection evaluates to the finite-coefficient projection.
Source: Stacks, sites-cohomology.tex, 0B56, 07A4, 07A6; Zheng Construction 4.1.
(blueprint: lem-pur-quotient-diagram-projection-evaluation).

Proof: construct the ordinary and derived quotient presentation with its actual
transition formulas. Evaluate the coefficient mate by the normalized counit square
and the inverse adjunction transpose formula. This gives the specified finite counit.
The ordinary tensor square gives equality on every cochain total-degree summand;
the three representative equations and the reduction evaluation equation then give
the source and target balance evaluation squares. Apply the general geometric
projection evaluation identity, whose proof transposes and uses the tensor-pullback
and counit evaluation squares. Substitute both balancing squares and the finite
coefficient mate. Naturality of the projection follows by transposing, applying
counit and tensor-comparison naturality, and transposing back. Combine this with
naturality of the coefficient mate and both balances. These equations and the
constructed transitions are precisely the fields of Laws. -/
theorem quotientDiagramProjectionEvaluation
    (J : GrothendieckTopology C) (K : GrothendieckTopology X)
    (A : Type (max c v r)) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf K (Type (max c v r)))
    (uPush : Sheaf K (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv] :
    ∃ p : Presentation.{c, v, r} J K A I uInv uPush adj, Laws.{c, v, r} p := by
  obtain ⟨p, hp⟩ := quotientDiagramProjectionConstruction.{c, v, r} J K A I uInv uPush adj
  have ht : p.quotient.TransitionFormula J (finite.{c, v, r} J A I)
      (quotientTransition.{c, v, r} J A I) p.source K uInv uPush adj :=
    push_transition_of_pull.{c, v, r} J (finite.{c, v, r} J A I)
    (quotientTransition.{c, v, r} J A I) p.source K uInv uPush adj p.quotient hp
  exact ⟨p, ht, hp, coefficient_counit p, arrow_evaluation p, arrow_naturality p⟩

end SheafOfModules.QuotientDiagramProjection
