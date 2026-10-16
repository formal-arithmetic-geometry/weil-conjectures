/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.AlgebraicGeometry.AffineComparisonEtaleCechSystem
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity

/-!
# Sections and cocycles of a simultaneous étale Čech presentation

Source: Stacks Project, Tags 099S, 099T and 099U; finite representatives and eventual equality
in filtered colimits, Tag 002W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.AffineEtaleCechSystem

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable {Y : Scheme.{u}} {V : Y.ProEt} {n : ℕ} {U : Fin n → Over V}
  {I : Type u} [SmallCategory I] (S : AffineEtaleCechSystem Y V U I)
  (J : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The ordinary ordered Čech complex at an étale stage. -/
noncomputable abbrev stageComplex (i : I) : CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  (Presheaf.cechComplex (fun b ↦ Over.mk (S.f i b))).obj J.obj

/-- Restriction along the geometric transition maps, in every Čech degree. -/
noncomputable def transition {i j : I} (a : i ⟶ j) :
    S.stageComplex J j ⟶ S.stageComplex J i :=
  CochainComplex.ofHom
    (fun k ↦ AddCommGrpCat.ofHom (AddMonoidHom.pi fun y ↦
      (J.obj.map (S.trans a k y).op).hom.comp (Pi.evalAddMonoidHom _ y))) (by
      intro k
      apply AddCommGrpCat.ext
      intro c
      funext y
      change ((S.stageComplex J i).d k (k + 1)
        (fun z ↦ J.obj.map (S.trans a k z).op (c z))) y =
        J.obj.map (S.trans a (k + 1) y).op ((S.stageComplex J j).d k (k + 1) c y)
      rw [Presheaf.cechComplex_d_apply, Presheaf.cechComplex_d_apply, map_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [map_zsmul]
      congr 1
      rw [← ConcreteCategory.comp_apply, ← J.obj.map_comp, ← op_comp,
        ← ConcreteCategory.comp_apply, ← J.obj.map_comp, ← op_comp]
      rw [S.trans_face])

/-- The filtered diagram of stage Čech complexes. -/
noncomputable def diagram : Iᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ where
  obj i := S.stageComplex J i.unop
  map a := S.transition J a.unop
  map_id i := by
    ext k : 1
    apply AddCommGrpCat.ext
    intro c
    funext y
    change J.obj.map (S.trans (𝟙 i.unop) k y).op (c y) = c y
    rw [S.trans_id, op_id, J.obj.map_id]
    rfl
  map_comp a b := by
    ext k : 1
    apply AddCommGrpCat.ext
    intro c
    funext y
    change J.obj.map (S.trans (b.unop ≫ a.unop) k y).op (c y) =
      J.obj.map (S.trans b.unop k y).op (J.obj.map (S.trans a.unop k y).op (c y))
    rw [S.trans_comp, op_comp, J.obj.map_comp]
    rfl

/-- The comparison unit, followed by restriction along the presentation cone. -/
noncomputable def toOriginal (i : I) :
    S.stageComplex J i ⟶ (Presheaf.cechComplex U).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj := by
  let F := ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj
  let η := ((comparisonAdjunction AddCommGrpCat.{u + 1} Y).unit.app J).hom
  refine CochainComplex.ofHom (fun k ↦ AddCommGrpCat.ofHom
    (AddMonoidHom.pi fun y ↦ ((F.map (S.π k y i).op).hom.comp
      (η.app (op ((S.nerve k y).obj i))).hom).comp (Pi.evalAddMonoidHom _ y))) ?_
  intro k
  apply AddCommGrpCat.ext
  intro c
  funext y
  change ((Presheaf.cechComplex U).obj F).d k (k + 1)
      (fun z ↦ F.map (S.π k z i).op (η.app _ (c z))) y =
    F.map (S.π (k + 1) y i).op (η.app _ ((S.stageComplex J i).d k (k + 1) c y))
  rw [Presheaf.cechComplex_d_apply, Presheaf.cechComplex_d_apply, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_zsmul, map_zsmul]
  congr 1
  have hη := ConcreteCategory.congr_hom
    (η.naturality (Presheaf.cechNerveMap (fun b ↦ Over.mk (S.f i b)) y l.succAbove).left.op)
    (c (y ∘ l.succAbove))
  change F.map (Presheaf.cechNerveMap U y l.succAbove).left.op
      (F.map (S.π k (y ∘ l.succAbove) i).op (η.app _ (c (y ∘ l.succAbove)))) = _
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, S.π_face,
    op_comp, F.map_comp]
  exact congrArg (fun x ↦ F.map (S.π (k + 1) y i).op x) hη.symm

/-- These maps form a cocone of complexes. -/
noncomputable def cocone : Cocone (S.diagram J) where
  pt := (Presheaf.cechComplex U).obj
    ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj
  ι.app i := S.toOriginal J i.unop
  ι.naturality i j a := by
    ext k : 1
    apply AddCommGrpCat.ext
    intro c
    funext y
    let F := ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj
    let η := ((comparisonAdjunction AddCommGrpCat.{u + 1} Y).unit.app J).hom
    change F.map (S.π k y j.unop).op
        (η.app _ (J.obj.map (S.trans a.unop k y).op (c y))) =
      F.map (S.π k y i.unop).op (η.app _ (c y))
    have hη := ConcreteCategory.congr_hom (η.naturality (S.trans a.unop k y).op) (c y)
    change η.app _ (J.obj.map (S.trans a.unop k y).op (c y)) =
      F.map ((Scheme.toProEt Y).map (S.trans a.unop k y)).op (η.app _ (c y)) at hη
    rw [hη, ← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, S.π_naturality]

/-- The section cocone on one repeated intersection. -/
noncomputable def sectionCocone (k : ℕ) (y : Fin (k + 1) → Fin n) :
    Cocone ((S.nerve k y).op ⋙ J.obj) where
  pt := ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj.obj
    (op (Presheaf.cechNerveObj U y).left)
  ι.app i := ((comparisonAdjunction AddCommGrpCat.{u + 1} Y).unit.app J).hom.app
    (op ((S.nerve k y).obj i.unop)) ≫
      ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj.map
        (S.π k y i.unop).op
  ι.naturality i j a := by
    let F := ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj
    let η := ((comparisonAdjunction AddCommGrpCat.{u + 1} Y).unit.app J).hom
    apply AddCommGrpCat.ext
    intro x
    change F.map (S.π k y j.unop).op
        (η.app _ (J.obj.map (S.trans a.unop k y).op x)) =
      F.map (S.π k y i.unop).op (η.app _ x)
    have hη := ConcreteCategory.congr_hom (η.naturality (S.trans a.unop k y).op) x
    change η.app _ (J.obj.map (S.trans a.unop k y).op x) =
      F.map ((Scheme.toProEt Y).map (S.trans a.unop k y)).op (η.app _ x) at hη
    rw [hη, ← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, S.π_naturality]

private noncomputable def sectionIsColimit [IsCofiltered I]
    (hS : ∀ k y, Nonempty (IsLimit
      ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone (S.nerveCone k y))))
    (k : ℕ) (y : Fin (k + 1) → Fin n) : IsColimit (S.sectionCocone J k y) := by
  let F := ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj
  let η := ((comparisonAdjunction AddCommGrpCat.{u + 1} Y).unit.app J).hom
  have : ∀ i, IsAffine ((S.nerve k y).obj i).left := fun i ↦ S.affine i k y
  let hF := (isColimit_comparisonUpperStar_mapCocone_of_isAffine
    AddCommGrpCat.{u + 1} J (S.nerve k y) (S.nerveCone k y) (hS k y).some).some
  have := isIso_comparisonAdjunction_unit AddCommGrpCat.{u + 1} Y
  let e : ((S.nerve k y).op ⋙ J.obj) ≅
      (S.nerve k y).op ⋙ (Scheme.toProEt Y).op ⋙ F :=
    NatIso.ofComponents (fun i ↦ asIso (η.app (op ((S.nerve k y).obj i.unop))))
      (fun a ↦ η.naturality ((S.nerve k y).map a.unop).op)
  exact (IsColimit.precomposeHomEquiv e _).symm hF

private theorem exists_cochain_rep [IsCofiltered I]
    (hS : ∀ k y, Nonempty (IsLimit
      ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone (S.nerveCone k y))))
    (k : ℕ) (c : (S.cocone J).pt.X k) :
    ∃ (i : Iᵒᵖ) (x : ((S.diagram J).obj i).X k),
      ((S.cocone J).ι.app i).f k x = c := by
  classical
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  have hr (y : Fin (k + 1) → Fin n) :=
    Concrete.isColimit_exists_rep _ (S.sectionIsColimit J hS k y) (c y)
  choose i x hx using hr
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  let a (y : Fin (k + 1) → Fin n) : i y ⟶ j := (hj (by simp)).some
  refine ⟨j, (fun y ↦ J.obj.map (S.trans (a y).unop k y).op (x y)), ?_⟩
  funext y
  have h := ConcreteCategory.congr_hom ((S.sectionCocone J k y).w (a y)) (x y)
  exact h.trans (hx y)

private theorem eventually_cochain_zero [IsCofiltered I]
    (hS : ∀ k y, Nonempty (IsLimit
      ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone (S.nerveCone k y))))
    (k : ℕ) (i : Iᵒᵖ) (x : ((S.diagram J).obj i).X k)
    (hx : ((S.cocone J).ι.app i).f k x = 0) :
    ∃ (j : Iᵒᵖ) (a : i ⟶ j), ((S.diagram J).map a).f k x = 0 := by
  classical
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  have hr (y : Fin (k + 1) → Fin n) :=
    Concrete.isColimit_exists_of_rep_eq _ (S.sectionIsColimit J hS k y)
      (x y) (0 : ((S.nerve k y).op ⋙ J.obj).obj i)
      (by have h := congrFun hx y
          change (S.sectionCocone J k y).ι.app i (x y) = 0 at h
          simpa only [map_zero] using h)
  choose j a b hab using hr
  obtain ⟨l, f, g, hg⟩ := IsFiltered.wideSpan a
  refine ⟨l, f, ?_⟩
  funext y
  have hz := congrArg (fun z ↦ J.obj.map (S.trans (g y).unop k y).op z) (hab y)
  change J.obj.map (S.trans (g y).unop k y).op
      (J.obj.map (S.trans (a y).unop k y).op (x y)) = _ at hz
  rw [map_zero, map_zero] at hz
  change J.obj.map (S.trans f.unop k y).op (x y) = 0
  rw [← hg y, unop_comp, S.trans_comp, op_comp, J.obj.map_comp]
  exact hz

/-- Finite cochains lift along section continuity; after a further stage their
finitely many coboundary components vanish. This gives a genuine stage cocycle.
Source: Stacks Project, Tag 099U, the two finite Čech limit reductions;
Tags 099S and 099T for continuity and the unit, and Tag 002W for filtered colimits.
(blueprint: lem-cbc-affine-cech-system-cocycle-lift).

Proof: Represent each coefficient by continuity and pass to a common stage using
filteredness and finiteness of the tuple set. The image of the differential is
zero since the comparison maps commute with the differential. Each component of
that differential is therefore eventually zero in its filtered section colimit.
A finite wide span gives a single further transition killing all components.
Transport the cochain along it; the chain-map identity proves it is a cocycle,
and cocone naturality preserves its image. Empty tuple sets obey the same argument. -/
theorem exists_cocycle_lift [IsCofiltered I]
    (hS : ∀ k y, Nonempty (IsLimit
      ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone (S.nerveCone k y))))
    (k : ℕ) (c : (S.cocone J).pt.X k)
    (hc : (S.cocone J).pt.d k (k + 1) c = 0) :
    ∃ (i : I) (x : (S.stageComplex J i).X k),
      (S.stageComplex J i).d k (k + 1) x = 0 ∧ (S.toOriginal J i).f k x = c := by
  obtain ⟨i, x, hx⟩ := S.exists_cochain_rep J hS k c
  have hz : ((S.cocone J).ι.app i).f (k + 1)
      (((S.diagram J).obj i).d k (k + 1) x) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← ((S.cocone J).ι.app i).comm]
    change (S.cocone J).pt.d k (k + 1) (((S.cocone J).ι.app i).f k x) = 0
    rw [hx]
    exact hc
  obtain ⟨j, a, ha⟩ := S.eventually_cochain_zero J hS (k + 1) i _ hz
  refine ⟨j.unop, ((S.diagram J).map a).f k x, ?_, ?_⟩
  · change ((S.diagram J).obj j).d k (k + 1) (((S.diagram J).map a).f k x) = 0
    rw [← ConcreteCategory.comp_apply, ((S.diagram J).map a).comm]
    exact ha
  · change (((S.diagram J).map a) ≫ (S.cocone J).ι.app j).f k x = c
    rw [(S.cocone J).w a]
    exact hx

end AlgebraicGeometry.ProEtale.AffineEtaleCechSystem
