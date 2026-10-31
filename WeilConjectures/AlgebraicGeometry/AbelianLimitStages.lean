/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.StageTransition
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.CommShiftPlus
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal

/-! # Stage comparisons with arbitrary abelian coefficients

The module-coefficient construction of `LimitStage` is extended to an arbitrary
Grothendieck abelian coefficient category, using `derivedBaseChangeMapPlus`.
Source: Stacks Tags 0EYM and 0GIU; the proof is the general-square pasting argument.
(blueprint: lem-sf-abelian-limit-stage-diagram).
-/

@[expose] public section

universe u' u

set_option autoImplicit false

open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.AbelianLimitStage

variable {B W : Scheme.{u}}

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

/-- The functor `K ↦ π^* Rg_* (w^* K)` attached to a stage. -/
noncomputable abbrev functor (α : LimitStage B W) :
    DerivedCategory.Plus (Sheaf W.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf B.smallEtaleTopology A) :=
  D+((α.w)^*[A]) ⋙ R+((α.g)_*[A]) ⋙
    D+((α.π)^*[A])

omit [HasSmallSiteSheafify A] in
lemma functor_obj (α : LimitStage B W)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) :
    (functor A α).obj K = D+((α.π)^*[A]).obj
      (R+((α.g)_*[A]).obj (D+((α.w)^*[A]).obj K)) := rfl

/-- The transition map of a morphism of stages `φ : α ⟶ β`, as a natural transformation:
`π_β^* Rg_{β*} w_β^* K ≅ π_α^* s^* Rg_{β*} w_β^* K ⟶ π_α^* Rg_{α*} t^* w_β^* K ≅
π_α^* Rg_{α*} w_α^* K`, the middle map being the pullback along `π_α` of the derived base-change
map of the square `(t, s)`. -/
noncomputable def transition {α β : LimitStage B W} (φ : LimitStage.Hom α β) :
    functor A β ⟶ functor A α :=
  Functor.whiskerLeft D+((β.w)^*[A])
      (Functor.whiskerLeft R+((β.g)_*[A])
        (upperStarCompDerivedPlus A α.π φ.s β.π φ.wπ.symm).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Etale.derivedBaseChangeMapPlus A ⟨φ.wg⟩)
        D+((α.π)^*[A]) ≫
      (Functor.associator _ _ _).hom) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (upperStarCompDerivedPlus A φ.t β.w α.w φ.ww.symm).inv
      (R+((α.g)_*[A]) ⋙ D+((α.π)^*[A]))

omit [HasSmallSiteSheafify A] in
lemma transition_app {α β : LimitStage B W} (φ : LimitStage.Hom α β)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) :
    (transition A φ).app K =
      (upperStarCompDerivedPlus A α.π φ.s β.π φ.wπ.symm).hom.app
          (R+((β.g)_*[A]).obj (D+((β.w)^*[A]).obj K)) ≫
        D+((α.π)^*[A]).map
          ((Etale.derivedBaseChangeMapPlus A ⟨φ.wg⟩).app
              (D+((β.w)^*[A]).obj K) ≫
            R+((α.g)_*[A]).map
              ((upperStarCompDerivedPlus A φ.t β.w α.w
                φ.ww.symm).inv.app K)) := by
  simp [transition]

/-- The transition maps compose: the transition map of a composite of morphisms of stages is
the composite of the transition maps. -/
lemma transition_comp {α β γ : LimitStage B W} (φ : LimitStage.Hom α β) (ψ : LimitStage.Hom β γ) :
    transition A ψ ≫ transition A φ = transition A (φ.comp ψ) := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  simp only [NatTrans.comp_app, transition_app]
  have hp := NatTrans.congr_app (Etale.derivedBaseChangeMapPlus_paste_horiz A
    (⟨ψ.wg⟩ : CommSq ψ.t β.g γ.g ψ.s)
    (⟨φ.wg⟩ : CommSq φ.t α.g β.g φ.s)
    (⟨(φ.comp ψ).wg⟩ : CommSq (φ.t ≫ ψ.t) α.g γ.g (φ.s ≫ ψ.s)))
    (D+((γ.w)^*[A]).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at hp
  -- associativity of the composition isomorphisms on the side of the bases
  have hS := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (A)
    α.π φ.s ψ.s β.π (φ.s ≫ ψ.s) γ.π φ.wπ.symm rfl ψ.wπ.symm)
    (R+((γ.g)_*[A]).obj (D+((γ.w)^*[A]).obj K))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hS
  -- associativity of the composition isomorphisms on the side of the coefficients
  have hW := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (A)
    φ.t ψ.t γ.w (φ.t ≫ ψ.t) β.w α.w rfl ψ.ww.symm (φ.comp ψ).ww.symm) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hW
  have hW' := congrArg Iso.inv (Iso.ext hW :
    (upperStarCompDerivedPlus A φ.t β.w α.w φ.ww.symm).app K ≪≫
      D+((φ.t)^*[A]).mapIso
        ((upperStarCompDerivedPlus A ψ.t γ.w β.w ψ.ww.symm).app K) =
    (upperStarCompDerivedPlus A (φ.t ≫ ψ.t) γ.w α.w
        (φ.comp ψ).ww.symm).app K ≪≫
      (upperStarCompDerivedPlus A φ.t ψ.t (φ.t ≫ ψ.t) rfl).app
        (D+((γ.w)^*[A]).obj K))
  simp only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv] at hW'
  rw [hp]
  have n1 := (upperStarCompDerivedPlus A α.π φ.s β.π φ.wπ.symm).hom.naturality
    ((Etale.derivedBaseChangeMapPlus A ⟨ψ.wg⟩).app (D+((γ.w)^*[A]).obj K) ≫
      R+((β.g)_*[A]).map
        ((upperStarCompDerivedPlus A ψ.t γ.w β.w ψ.ww.symm).inv.app K))
  have n2 := congrArg D+((α.π)^*[A]).map
    ((Etale.derivedBaseChangeMapPlus A ⟨φ.wg⟩).naturality
      ((upperStarCompDerivedPlus A ψ.t γ.w β.w ψ.ww.symm).inv.app K))
  have n3 := congrArg (fun x ↦ D+((α.π)^*[A]).map
    (R+((α.g)_*[A]).map x)) hW'
  simp only [Functor.comp_map, Functor.map_comp] at n1 n2 n3
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% n1, ← reassoc_of% hS]
  rw [reassoc_of% n2, n3]

/-- The transition map of the identity morphism of a stage is the identity. -/
lemma transition_id (α : LimitStage B W) : transition A (LimitStage.Hom.id α) = 𝟙 _ := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  have h1 := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_id_right (A)
    α.π) (R+((α.g)_*[A]).obj (D+((α.w)^*[A]).obj K))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app] at h1
  have h2 := Etale.upperStarCompDerivedPlus_id_left_inv_app (A) α.w K
  have h3 : (Etale.derivedBaseChangeMapPlus A ⟨(LimitStage.Hom.id α).wg⟩).app
      (D+((α.w)^*[A]).obj K) =
      (upperStarIdDerivedPlus A α.S).hom.app
          (R+((α.g)_*[A]).obj (D+((α.w)^*[A]).obj K)) ≫
        R+((α.g)_*[A]).map
          ((upperStarIdDerivedPlus A α.T).inv.app
            (D+((α.w)^*[A]).obj K)) := by
    rw [Etale.derivedBaseChangeMapPlus_id]
    simp
  rw [transition_app, h3]
  simp only [Category.assoc, ← Functor.map_comp, h2, CategoryTheory.Functor.map_id,
    NatTrans.id_app]
  refine Eq.trans ?_ h1
  congr 2
  exact Category.comp_id _


noncomputable instance (α : LimitStage B W) : (functor A α).CommShift ℤ := by
  dsimp only [functor]
  infer_instance

instance (α : LimitStage B W) : (functor A α).IsTriangulated := by
  dsimp only [functor]
  infer_instance

instance {α β : LimitStage B W} (φ : LimitStage.Hom α β) :
    NatTrans.CommShift (transition A φ) ℤ := by
  dsimp only [transition]
  infer_instance

end AlgebraicGeometry.Etale.AbelianLimitStage

namespace AlgebraicGeometry.Etale.AbelianLimitStageSystem

variable {B W : Scheme.{u}} {I : Type u} [Category.{u} I]
  (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  (S : LimitStageSystem B W I)

/-- The derived diagram attached to a system of stages and a fixed coefficient complex. -/
noncomputable def derivedDiagram
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) :
    Iᵒᵖ ⥤ DerivedCategory.Plus (Sheaf B.smallEtaleTopology A) where
  obj i := (AbelianLimitStage.functor A (S.obj i.unop)).obj K
  map f := (AbelianLimitStage.transition A (S.map f.unop)).app K
  map_id i := by
    rw [unop_id, S.map_id, AbelianLimitStage.transition_id, NatTrans.id_app]
  map_comp f g := by
    rw [← NatTrans.comp_app, AbelianLimitStage.transition_comp, unop_comp, S.map_comp]

/-- The canonical cocone to the derived functor of the limit stage. -/
noncomputable def derivedCocone
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) :
    Cocone (derivedDiagram A S K) where
  pt := (AbelianLimitStage.functor A S.pt).obj K
  ι :=
    { app i := (AbelianLimitStage.transition A (S.π i.unop)).app K
      naturality i j f := by
        simp only [derivedDiagram, Functor.const_obj_obj, Functor.const_obj_map,
          Category.comp_id, ← NatTrans.comp_app, AbelianLimitStage.transition_comp, S.w] }

/-- The sheaf cohomology diagram in degree `q`. -/
noncomputable def diagram
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) (q : ℤ) :
    Iᵒᵖ ⥤ Sheaf B.smallEtaleTopology A :=
  derivedDiagram A S K ⋙ DerivedCategory.Plus.homologyFunctor _ q

/-- The cohomology cocone in degree `q`. -/
noncomputable def cocone
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) (q : ℤ) :
    Cocone (diagram A S K q) :=
  (DerivedCategory.Plus.homologyFunctor _ q).mapCocone (derivedCocone A S K)

/-- The canonical continuity comparison from the colimit of the degree-`q` diagram. -/
noncomputable def comparison
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) (q : ℤ) :
    colimit (diagram A S K q) ⟶ (cocone A S K q).pt :=
  colimit.desc _ (cocone A S K q)

end AlgebraicGeometry.Etale.AbelianLimitStageSystem


namespace AlgebraicGeometry.Etale

open Opposite

/-- The stage system above a fixed index, with its coefficient maps to that index.
Source: Stacks Tag 0GIU, passage to the tail above the stage of definition.
(blueprint: lem-sf-abelian-limit-stage-diagram). -/
noncomputable def relativeLimitStageSystem
    {I : Type u} [Preorder I] (DU DB : Iᵒᵖ ⥤ Scheme.{u}) (η : DU ⟶ DB)
    (cU : Cone DU) (cB : Cone DB) (g : cU.pt ⟶ cB.pt)
    (hg : ∀ i : Iᵒᵖ, cU.π.app i ≫ η.app i = g ≫ cB.π.app i) (i₀ : I) :
    LimitStageSystem cB.pt (DU.obj (op i₀)) (Set.Ici i₀)ᵒᵖ where
  obj i :=
    { T := DU.obj (op i.unop.val)
      S := DB.obj (op i.unop.val)
      g := η.app (op i.unop.val)
      π := cB.π.app (op i.unop.val)
      w := DU.map (homOfLE i.unop.property : i₀ ⟶ i.unop.val).op }
  map {i j} f :=
    { t := DU.map (homOfLE (leOfHom f.unop) : j.unop.val ⟶ i.unop.val).op
      s := DB.map (homOfLE (leOfHom f.unop) : j.unop.val ⟶ i.unop.val).op
      wg := η.naturality _
      wπ := cB.w _
      ww := by rw [← DU.map_comp]; congr 1 }
  map_id i := by
    apply LimitStage.Hom.ext
    · simp
    · simp
  map_comp f h := by
    apply LimitStage.Hom.ext
    · dsimp only [LimitStage.Hom.comp]
      rw [← DU.map_comp]; congr 1
    · dsimp only [LimitStage.Hom.comp]
      rw [← DB.map_comp]; congr 1
  pt :=
    { T := cU.pt
      S := cB.pt
      g := g
      π := 𝟙 cB.pt
      w := cU.π.app (op i₀) }
  π i :=
    { t := cU.π.app (op i.unop.val)
      s := cB.π.app (op i.unop.val)
      wg := hg _
      wπ := Category.id_comp _
      ww := cU.w _ }
  w f := by
    apply LimitStage.Hom.ext
    · exact cU.w _
    · exact cB.w _

end AlgebraicGeometry.Etale
