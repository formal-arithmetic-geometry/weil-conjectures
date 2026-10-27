/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Order.Directed

/-! # Connected towers of finite abelian covers

Source: Bhatt--Scholze, Sections 4.2 and 5.1, finite connected torsor descent
(blueprint: def-sfb-connected-abelian-cover-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- The geometric and group inverse systems, their limits and the specified torsor
comparisons. Finite profinite test objects are precisely disjoint labelled copies.
Both comparison conventions are `(x,g) ↦ (x,gx)`. The last equation expresses
compatibility on the entire profinite parameter scheme.
Source: Bhatt--Scholze, Sections 4.2 and 5.1, finite connected torsor descent
(blueprint: def-sfb-connected-abelian-cover-tower). -/
structure ConnectedAbelianCoverTower (U : Scheme.{u}) (I : Type u)
    [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] where
  levels : Iᵒᵖ ⥤ U.ProEt
  groups : Iᵒᵖ ⥤ ProfiniteGrp.{u}
  finite_groups : ∀ i, Finite (groups.obj i)
  commutative : ∀ i (g h : groups.obj i), g * h = h * g
  surjective : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), Function.Surjective (groups.map f)
  affine : ∀ i, IsAffine (levels.obj i).left
  connected : ∀ i, ConnectedSpace (levels.obj i).left
  finite : ∀ i, IsFinite (levels.obj i).hom
  etale : ∀ i, Etale (levels.obj i).hom
  action : ∀ i, groups.obj i →* End (levels.obj i)
  equivariant : ∀ {i j : Iᵒᵖ} (f : i ⟶ j) (g : groups.obj i),
    action i g ≫ levels.map f = levels.map f ≫ action j (groups.map f g)
  finiteComparison : ∀ i,
    Scheme.UniversalCover.profiniteProduct (levels.obj i).left
      ((forget₂ ProfiniteGrp Profinite).obj (groups.obj i)) ≅
        pullback (levels.obj i).hom (levels.obj i).hom
  finite_fst : ∀ i, (finiteComparison i).hom ≫ pullback.fst _ _ =
    Scheme.UniversalCover.profiniteProductBase _ _
  finite_action : ∀ i (g : groups.obj i),
    Scheme.UniversalCover.profiniteProductSection _ _ g ≫
      (finiteComparison i).hom ≫ pullback.snd _ _ = (action i g).left
  cone : Cone levels
  isLimit : IsLimit ((Scheme.ProEt.forget U ⋙ Over.forget U).mapCone cone)
  limit_connected : ConnectedSpace cone.pt.left
  cover : Presieve.singleton cone.pt.hom ∈ Scheme.proetalePrecoverage U
  groupCone : Cone groups
  groupIsLimit : IsLimit groupCone
  comparison : Scheme.UniversalCover.profiniteProduct cone.pt.left
    ((forget₂ ProfiniteGrp Profinite).obj groupCone.pt) ≅
      pullback cone.pt.hom cone.pt.hom
  comparison_fst : comparison.hom ≫ pullback.fst _ _ =
    Scheme.UniversalCover.profiniteProductBase _ _
  compatibility : ∀ i,
    comparison.hom ≫ pullback.snd _ _ ≫ (cone.π.app i).left =
      Scheme.UniversalCover.profiniteProductMap (cone.π.app i).left
        ((forget₂ ProfiniteGrp Profinite).map (groupCone.π.app i)) ≫
          (finiteComparison i).hom ≫ pullback.snd _ _

end AlgebraicGeometry.ProEtale
