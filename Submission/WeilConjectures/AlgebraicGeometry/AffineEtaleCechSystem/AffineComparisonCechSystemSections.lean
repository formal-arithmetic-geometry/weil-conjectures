/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.AffineComparisonEtaleCechSystem
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Submission.WeilConjectures.CategoryTheory.Sites.CechComplex
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

end AlgebraicGeometry.ProEtale.AffineEtaleCechSystem
