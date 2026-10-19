/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

import Sheaf.AlgebraicGeometry.Sites.AffineLimitSheafReconstruction
import Mathlib.CategoryTheory.Limits.Final

/-!
# Descent of torsion étale sheaves along affine inverse limits

Source: Stacks Project, Tag 0EYN (via Tags 0EXJ and 0EYL)
(blueprint: lem-kun-descent-limit).

## Main definitions

* `kunDescentStageTransition`: the canonical adjoint transition between stage sheaves.
* `kunDescentPullPushTransition`: the induced transition on the limit scheme.

## Main statements

* `kun_descent_limit`: stage compatibility and the canonical colimit reconstruction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The canonical transition from the inverse image of the stage-i direct image to the
stage-j direct image.  It is the adjoint of the inverse direct-image composition comparison,
so no transition morphism is chosen arbitrarily.

Source: Stacks Project, Tag 0EXJ, first paragraph; Tag 0EYN, part (1)
(blueprint: lem-kun-descent-limit).
-/
noncomputable def kunDescentStageTransition
    {I : Type u} [Preorder I] (X : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone X)
    (F : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    {i j : I} (f : i ⟶ j) :
    (Etale.upperStar AddCommGrpCat.{u + 1} (X.map f.op)).obj
        ((Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F) ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op j))).obj F :=
  ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    (X.map f.op)).homEquiv _ _).symm
      ((Etale.lowerStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (X.map f.op)
        (c.π.app (op i)) (c.w f.op).symm).inv.app F)

/-- The canonical transition between the pull-push sheaves on the limit.  First use
inverse-image composition, then pull back the canonical stage transition.

Source: Stacks Project, Tag 0EXJ, transition maps in the statement
(blueprint: lem-kun-descent-limit).
-/
noncomputable def kunDescentPullPushTransition
    {I : Type u} [Preorder I] (X : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone X)
    (F : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    {i j : I} (f : i ⟶ j) :
    (Etale.upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj
        ((Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F) ⟶
      (Etale.upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).obj
        ((Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op j))).obj F) :=
  (Etale.upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (X.map f.op)
    (c.π.app (op i)) (c.w f.op).symm).hom.app
      ((Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F) ≫
    (Etale.upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map
      (kunDescentStageTransition X c F f)

private lemma homEquiv_paste {S T U : Scheme.{u}} (p : U ⟶ T) (f : T ⟶ S)
    (r : U ⟶ S) (hr : r = p ≫ f)
    (A : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (B : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (C : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : (Etale.upperStar AddCommGrpCat f).obj A ⟶ B)
    (b : (Etale.upperStar AddCommGrpCat p).obj B ⟶ C) :
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat r).homEquiv _ _
        ((Etale.upperStarComp AddCommGrpCat.{u + 1} p f r hr).hom.app A ≫
          (Etale.upperStar AddCommGrpCat p).map a ≫ b) =
      (Etale.upperStarLowerStarAdjunction AddCommGrpCat f).homEquiv _ _ a ≫
        (Etale.lowerStar AddCommGrpCat f).map
          ((Etale.upperStarLowerStarAdjunction AddCommGrpCat p).homEquiv _ _ b) ≫
        (Etale.lowerStarComp AddCommGrpCat.{u + 1} p f r hr).hom.app C := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [Etale.upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} p f A r hr]
  simp only [Adjunction.comp_unit_app, Functor.comp_obj, Category.assoc]
  rw [← (Etale.lowerStarComp AddCommGrpCat.{u + 1} p f r hr).hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← (Etale.lowerStarComp AddCommGrpCat.{u + 1} p f r hr).hom.naturality]
  rw [← Functor.map_comp_assoc]
  have hn := (Etale.upperStarLowerStarAdjunction AddCommGrpCat p).unit.naturality a
  change a ≫ (Etale.upperStarLowerStarAdjunction AddCommGrpCat p).unit.app B =
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat p).unit.app
        ((Etale.upperStar AddCommGrpCat f).obj A) ≫
      (Etale.lowerStar AddCommGrpCat p).map ((Etale.upperStar AddCommGrpCat p).map a) at hn
  rw [← hn]
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc]

private lemma kunDescentPullPushTransition_eq_approximationMap
    {I : Type u} [Preorder I] (X : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone X)
    (F : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    {i j : I} (f : i ⟶ j) :
    kunDescentPullPushTransition X c F f =
      Etale.AffineLimitSheafApproximation.approximationMap
        (c.π.app (op j)) (X.map f.op) (c.π.app (op i)) (c.w f.op).symm F := by
  apply ((Etale.upperStarLowerStarAdjunction AddCommGrpCat (c.π.app (op i))).homEquiv _ _).injective
  rw [Etale.AffineLimitSheafApproximation.approximationMap, Equiv.apply_symm_apply]
  have h := homEquiv_paste (c.π.app (op j)) (X.map f.op) (c.π.app (op i))
    (c.w f.op).symm _ _ _ (kunDescentStageTransition X c F f) (𝟙 _)
  simpa only [kunDescentPullPushTransition, Category.comp_id, kunDescentStageTransition,
    Equiv.apply_symm_apply, Adjunction.homEquiv_id] using h

private lemma stageTransition_id {S T : Scheme.{u}} (p : T ⟶ S)
    (f : S ⟶ S) (hf : f = 𝟙 S) (hp : p = p ≫ f)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat f).homEquiv _ _).symm
        ((Etale.lowerStarComp AddCommGrpCat.{u + 1} p f p hp).inv.app F) =
      eqToHom (congrArg (fun a : S ⟶ S ↦
        (Etale.upperStar AddCommGrpCat a).obj ((Etale.lowerStar AddCommGrpCat p).obj F)) hf) ≫
        (Etale.upperStarId AddCommGrpCat.{u + 1} S).hom.app
          ((Etale.lowerStar AddCommGrpCat p).obj F) := by
  subst f
  simp only [eqToHom_refl, Category.id_comp]
  apply ((Etale.upperStarLowerStarAdjunction AddCommGrpCat (𝟙 S)).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit,
    Etale.upperStarId_hom_app_unit_app, Etale.lowerStarComp_id_right]
  simp

/-- The direct images of a torsion abelian étale sheaf along an affine inverse limit form
the canonical compatible system, and the counit cocone of its pulled-back system is a
colimit cocone.  In particular its induced canonical colimit-to-sheaf map is an isomorphism.
The stage identity and composition clauses use the canonical inverse-image comparisons;
the existential diagram is indexed by the directed category `I`, not its opposite.

Source: Stacks Project, Tag 0EYN, via Tags 0EXJ and 0EYL
(blueprint: lem-kun-descent-limit).

1. Affine stages are qcqs and the projections are affine
   (`lem-weil-pbc-affine-scheme-qcqs`, `lem-weil-pbc-limit-affine-transition`).
   The affine-etale-site colimit theorem gives a coherent strict finite-cover site system
   whose colimit is the limit's affine etale site. Restricting to these sites is an
   equivalence on abelian sheaves (`lem-weil-pbc-affine-etale-site-colimit`,
   `lem-weil-pbc-affine-etale-site-topos`).
2. Direct images on an affine object are sections over its base change; these identify
   the geometric and site direct images, naturally in objects and sheaves. By their
   adjunctions the inverse images are identified too, compatibly with units and counits.
3. Define the stage transitions as the adjoints of the direct-image composition
   comparisons. The composite-adjunction counit formula proves the identity and cocycle
   clauses (`lem-cat-right-adjoint-composition`, `lem-weil-pbc-inverse-image-composition`).
   Pulling back gives a functor on `I`; the same formula makes the counits a cocone.
4. Abelian etale sheaves have small colimits
   (`lem-weil-pbc-abelian-etale-sheaves-grothendieck`), transported through the site
   equivalence by its Hom bijections. The counit cocone induces its canonical map to `F`.
5. Descend each affine etale object to a stage. The abelian section formula
   (`lem-weil-pbc-colimit-of-sites-sections`, Tag 09YN) computes sections of that colimit
   over the nonempty directed tail of later stages, with its specified unit maps.
6. On this tail every term identifies with the same group of sections of `F` and every
   transition is the identity, by the adjunction triangle identity. The induced counit
   map is likewise the identity on each term. A constant identity diagram over a
   nonempty directed tail has its value as colimit, hence this particular map is an iso.
7. The sectionwise inverses commute with restrictions, so give an inverse sheaf morphism.
   Transport back through the affine-site equivalences; the comparisons preserve the
   transitions and counits, proving that the displayed counit cocone is colimiting.
-/
theorem kun_descent_limit
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (X : Iᵒᵖ ⥤ Scheme.{u})
    (hX : ∀ i : Iᵒᵖ, IsAffine (X.obj i))
    (htransition : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (X.map f))
    (c : Cone X) (hc : IsLimit c)
    (F : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : CategoryTheory.Sheaf.IsTorsion F) :
    (∀ i : I, kunDescentStageTransition X c F (𝟙 i) =
      eqToHom (congrArg (fun a : X.obj (op i) ⟶ X.obj (op i) ↦
        (Etale.upperStar AddCommGrpCat.{u + 1} a).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F))
        (X.map_id (op i))) ≫
      (Etale.upperStarId AddCommGrpCat.{u + 1} (X.obj (op i))).hom.app
        ((Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F)) ∧
    (∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k),
      kunDescentStageTransition X c F (f ≫ g) =
        (Etale.upperStarComp AddCommGrpCat.{u + 1} (X.map g.op) (X.map f.op)
          (X.map (f ≫ g).op) (X.map_comp g.op f.op)).hom.app
            ((Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F) ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} (X.map g.op)).map
          (kunDescentStageTransition X c F f) ≫ kunDescentStageTransition X c F g) ∧
    ∃ (D : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
      (e : ∀ i : I, D.obj i ≅
        (Etale.upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F))
      (ι : D ⟶ (Functor.const I).obj F),
      (∀ {i j : I} (f : i ⟶ j),
        (e i).inv ≫ D.map f ≫ (e j).hom = kunDescentPullPushTransition X c F f) ∧
      (∀ i : I, ι.app i = (e i).hom ≫
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          (c.π.app (op i))).counit.app F) ∧
      Nonempty (IsColimit (Cocone.mk F ι)) := by
  classical
  have _hF := hF
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact stageTransition_id (c.π.app (op i)) (X.map (𝟙 i).op)
      (X.map_id (op i)) (c.w (𝟙 i).op).symm F
  · intro i j k f g
    apply ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (X.map (f ≫ g).op)).homEquiv _ _).injective
    rw [homEquiv_paste (X.map g.op) (X.map f.op) (X.map (f ≫ g).op)
      (X.map_comp g.op f.op)]
    simp only [kunDescentStageTransition, Equiv.apply_symm_apply]
    have he :
        Functor.isoWhiskerRight
            (Etale.lowerStarComp AddCommGrpCat.{u + 1} (c.π.app (op k))
              (X.map g.op) (c.π.app (op j)) (c.w g.op).symm)
              (Etale.lowerStar AddCommGrpCat.{u + 1} (X.map f.op)) ≪≫
          Etale.lowerStarComp AddCommGrpCat.{u + 1} (c.π.app (op j))
            (X.map f.op) (c.π.app (op i)) (c.w f.op).symm =
        Functor.isoWhiskerLeft (Etale.lowerStar AddCommGrpCat.{u + 1} (c.π.app (op k)))
            (Etale.lowerStarComp AddCommGrpCat.{u + 1} (X.map g.op) (X.map f.op)
              (X.map (f ≫ g).op) (X.map_comp g.op f.op)) ≪≫
          Etale.lowerStarComp AddCommGrpCat.{u + 1} (c.π.app (op k))
            (X.map (f ≫ g).op) (c.π.app (op i)) (c.w (f ≫ g).op).symm := by
      apply Iso.ext
      exact Etale.lowerStarComp_assoc' AddCommGrpCat.{u + 1}
        (c.π.app (op k)) (X.map g.op) (X.map f.op) (c.π.app (op j))
        (X.map (f ≫ g).op) (c.π.app (op i)) (c.w g.op).symm
        (X.map_comp g.op f.op) (c.w f.op).symm
    have hei := congrArg (fun e ↦ e.inv.app F) he
    simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app] at hei
    rw [← Category.assoc, hei, Category.assoc]
    simp
  · let (i : Iᵒᵖ) : IsAffine (X.obj i) := hX i
    let {i j : Iᵒᵖ} (f : i ⟶ j) : IsAffineHom (X.map f) := htransition f
    let A := Etale.AffineLimitSheafApproximation.approximationDiagram X c F
    let K := Etale.AffineLimitSheafApproximation.approximationCocone X c F
    let E := (opOpEquivalence I).inverse
    obtain ⟨hA⟩ := Scheme.nonempty_isColimit_affineLimitSheafApproximation X c hc F
    have hK : IsColimit (K.whisker E) :=
      (Functor.Final.isColimitWhiskerEquiv E K).symm hA
    let D := E ⋙ A
    refine ⟨D, (fun i => Iso.refl _), (K.whisker E).ι, ?_, ?_, ?_⟩
    · intro i j f
      change A.map (E.map f) = kunDescentPullPushTransition X c F f
      exact (kunDescentPullPushTransition_eq_approximationMap X c F f).symm
    · intro i
      rfl
    · exact ⟨hK⟩

end AlgebraicGeometry
