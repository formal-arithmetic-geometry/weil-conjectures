/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-! # Same-universe inverse image of abelian etale sheaves

## References

* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/-- Direct image on abelian etale sheaves admits an inverse-image left adjoint,
without increasing the universe of the coefficient groups. -/
theorem strictHenselian_stalkSections_comparison_functor
    {X Y : Scheme.{u + 1}} (g : Y ⟶ X) :
    ∃ H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1},
      Nonempty (H ⊣ g.Etale.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        X.smallEtaleTopology Y.smallEtaleTopology) := by
  let e := (equivSmallModel X.AffineEtale).inverse
  let J := e.inducedTopology (Scheme.AffineEtale.topology X)
  have : e.IsContinuous J (Scheme.AffineEtale.topology X) := by
    dsimp [e, J]
    infer_instance
  let i := e ⋙ Scheme.AffineEtale.Spec X
  have : i.IsContinuous J X.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ (Scheme.AffineEtale.topology X) _
  have : (i ⋙ g.Etale).IsContinuous J Y.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ X.smallEtaleTopology _
  have : ((i ⋙ g.Etale).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      J Y.smallEtaleTopology).IsRightAdjoint := by infer_instance
  have : (e.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      J (Scheme.AffineEtale.topology X)).IsEquivalence := by
    dsimp [e, J]
    infer_instance
  have : (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      J X.smallEtaleTopology).IsEquivalence := by
    exact Functor.isEquivalence_of_iso
      (Functor.sheafPushforwardContinuousComp e (Scheme.AffineEtale.Spec X)
        AddCommGrpCat.{u + 1} J (Scheme.AffineEtale.topology X) X.smallEtaleTopology)
  have : (g.Etale.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      X.smallEtaleTopology Y.smallEtaleTopology).IsRightAdjoint := by
    apply (Functor.isRightAdjoint_comp_iff_left _
      (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J X.smallEtaleTopology)).mp
    exact Functor.isRightAdjoint_of_iso
      (Functor.sheafPushforwardContinuousComp i g.Etale AddCommGrpCat.{u + 1}
        J X.smallEtaleTopology Y.smallEtaleTopology).symm
  exact Functor.IsRightAdjoint.exists_leftAdjoint
