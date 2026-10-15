/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CartesianChartClassPullback
import Sheaf.AlgebraicGeometry.CofilteredAffineEtaleModel
import Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit

/-! # Descent of raw classes with bounded-below coefficients

Source: Stacks Project, Tags 0EYL, 0EYM and 0GIT.
(blueprint: lem-sc-raw-derived-class-affine-descent).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

attribute [local irreducible] restrictedOverCohomologyMap
  cartesianDerivedImageMap cartesianChartCohomologyLift cartesianChartCohomologyIso
  upperStar upperStarCompDerivedPlus

set_option backward.isDefEq.respectTransparency true

/-- A raw derived class descends with its coefficient complex fixed at the original stage.

Source: Stacks Project, Tags 0EYL and 0GIT.
(blueprint: lem-sc-raw-derived-class-affine-descent).

Proof: Restrict the diagram to arrows into i. Descend V to an affine etale object
at a stage j using finite presentation. The base changes of this object form a
limiting diagram of qcqs schemes with affine transitions. Pull back the fixed
bounded-below complex K to this diagram and apply derived etale cohomology
continuity in degree q. A raw Hom from the degree-zero free representable computes
this hypercohomology: use a bounded-below injective representative of K and the
free-representable sections adjunction. Surjectivity of the filtered colimit map
gives a stage l and a class y. Inverse-image composition, the single comparison
and the shift comparison identify its image with the displayed chart pullback.
The equations defining the cone give the displayed coefficient isomorphism.
No direct image, exchange map, cartesian source, or restricted sheaf cohomology
is involved. Empty V and q=0 are included by the same adjunction and continuity.
-/
theorem exists_rawDerivedClass_affine_descent
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    (q : ℕ) (i : I) (V : c.pt.left.Etale) [IsAffine V.left]
    (K : DerivedCategory.Plus (Sheaf (D.obj i).left.smallEtaleTopology
      AddCommGrpCat.{u + 1}))
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree c.pt.left).obj V) ⟶
        ((D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj K)⟦(q : ℤ)⟧) :
    ∃ (j : I) (W : (D.obj j).left.Etale) (_ : IsAffine W.left)
      (r : V.left ⟶ W.left)
      (hr : IsPullback r V.hom W.hom (c.π.app j).left)
      (l : Over j) (b : l.left ⟶ i)
      (y : (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((((D.map l.hom).left)^*[AddCommGrpCat.{u + 1}]).obj
          ((abelianComparisonFree (D.obj j).left).obj W)) ⟶
        ((D+(((D.map b).left)^*[AddCommGrpCat.{u + 1}])).obj K)⟦(q : ℤ)⟧),
      z ≫ (shiftFunctor _ (q : ℤ)).map
          ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
            (c.π.app l.left).left (D.map b).left (c.π.app i).left
            (congrArg (fun t ↦ t.left) (c.w b)).symm).hom.app K) =
        cartesianChartClassPullback (D.map l.hom).left (c.π.app l.left).left
          (c.π.app j).left (congrArg (fun t ↦ t.left) (c.w l.hom)).symm
          W V r hr _ (q : ℤ) y := by
  sorry

end AlgebraicGeometry.Etale
