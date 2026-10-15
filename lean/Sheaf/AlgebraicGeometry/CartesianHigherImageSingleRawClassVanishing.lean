/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CartesianHigherImageTransitions
public import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility

/-! # Eventual vanishing of one raw cartesian derived class

Source: Stacks Project, Tags 0EYM, 0EYL and 0GIT.
(blueprint: stage3-cartesian-higher-image-single-raw-class-vanishing).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- A single raw cartesian derived class killed at the limit is killed at a later stage.

Source: Stacks Project, Tags 0EYM, 0EYL and 0GIT. Apply affine cohomology continuity
to the descended qcqs chart system and identify its transition with the displayed
raw map by exchange naturality.
(blueprint: stage3-cartesian-higher-image-single-raw-class-vanishing).

The proof is the affine cohomology continuity argument for one test object: descend the
finite-presentation chart and the raw derived class, apply continuity of the resulting
bounded-below cohomology system, and identify the resulting stage map with the displayed
cartesian transition by exchange naturality. This is strictly the one-class case; no
finite-family equalization is included. Empty affine objects and degree zero are covered
by the same construction.
-/
theorem exists_cartesianHigherImage_single_raw_class_eq_zero
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (i : I) (V : c.pt.left.Etale) [IsAffine V.left]
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree c.pt.left).obj V) ⟶
        ((D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj
          (cartesianDerivedImage f (D.obj i).hom
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧)
    (hz : z ≫ (shiftFunctor _ (q : ℤ)).map
      (cartesianDerivedImageMap f (D.obj i).hom c.pt.hom (c.π.app i).left
        (Over.w (c.π.app i)).symm ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) = 0) :
    ∃ (j : I) (a : j ⟶ i),
      z ≫ (shiftFunctor _ (q : ℤ)).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
          (c.π.app j).left (D.map a).left (c.π.app i).left
          (congrArg (fun b ↦ b.left) (c.w a)).symm).hom.app _ ≫
          (D+(((c.π.app j).left)^*[AddCommGrpCat.{u + 1}])).map
            (cartesianDerivedImageMap f (D.obj i).hom (D.obj j).hom
              (D.map a).left (Over.w (D.map a)).symm
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) = 0 := by
  sorry

end AlgebraicGeometry.Etale
