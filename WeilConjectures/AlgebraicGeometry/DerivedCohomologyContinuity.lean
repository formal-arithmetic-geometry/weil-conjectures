/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Final

/-! # Continuity for bounded-below étale complexes from a fixed stage

Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-prop-sf-comparison/lem-weil-pbc-derived-cohomology-continuity.md;
Stacks Project, Étale Cohomology, Tag 0GIT.
(blueprint: lem-weil-pbc-derived-cohomology-continuity).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical restriction from the colimit of the cohomology of the inverse images
of a fixed bounded-below complex is an isomorphism in every integer degree.
The index `Over i` records an arrow `a : j ⟶ i`, so all ways of pulling back from `i`
are retained. The isomorphisms `e` and `eY` allow presentations of the cohomology groups;
`hm` and `hs` specify their maps by the derived adjunction unit, the Leray isomorphism,
and inverse-image composition. Thus no arbitrary transition or restriction map is used.

Source: blueprint, sec-proetale-coefficients, sk-prop-sf-comparison,
lem-weil-pbc-derived-cohomology-continuity; Stacks Project, Tag 0GIT.
(blueprint: lem-weil-pbc-derived-cohomology-continuity).

Proof: (1) The slice `Over i` is cofiltered. Its forgetful functor is initial:
common predecessors give the existence condition and equalizing parallel arrows gives
the equalization condition of lem-weil-pbc-initial-functor-cofiltered-criterion.
By lem-weil-pbc-initial-functor-limit, restricting `c` along this functor preserves
its limit property. (2) Regard this restricted diagram as schemes over `D.obj i`,
with structure maps `D.map a.hom`. The cone equations give the compatible limit
structure map `c.π.app i`. Apply lem-weil-pbc-derived-etale-cohomology-limit to `K`
and `n`. This gives the colimit property of `s`; it requires neither torsion nor
finite coefficients. (3) By def-weil-pbc-etale-cohomology these groups are the
homology of derived global sections. By def-weil-pbc-category-colimit the induced
map is `colimit.desc F s`, followed by the specified identification `eY.hom`.
The colimit property makes this canonical restriction an isomorphism. -/
theorem derivedEtaleCohomology_fixedStage_continuity
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, CompactSpace (D.obj j)] [∀ j : I, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : I} (f : j ⟶ k), IsAffineHom (D.map f)]
    (i : I)
    (K : DerivedCategory.Plus (Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) (F : (Over i)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (e : ∀ a : Over i, F.obj (op a) ≅
      (Etale.cohomology AddCommGrpCat.{u + 1} (D.obj a.left) n).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} (D.map a.hom)).mapDerivedCategory.obj
          K.obj))
    (hm : ∀ {a b : Over i} (f : a ⟶ b), F.map f.op =
      (e b).hom ≫
      (Etale.cohomology AddCommGrpCat.{u + 1} (D.obj b.left) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          (D.map f.left)).unit.app
            ((Etale.upperStar AddCommGrpCat.{u + 1} (D.map b.hom)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{u + 1} (D.map f.left)).hom.app
            ((Etale.upperStar AddCommGrpCat.{u + 1} (D.map f.left)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{u + 1} (D.map b.hom)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology AddCommGrpCat.{u + 1} (D.obj a.left) n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{u + 1} (D.map f.left) (D.map b.hom)
            (D.map a.hom)
            ((congrArg D.map (Over.w f)).symm.trans (D.map_comp f.left b.hom))) ≪≫
          Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{u + 1} (D.map b.hom))
            (Etale.upperStar AddCommGrpCat.{u + 1} (D.map f.left))).inv.app K.obj) ≫
      (e a).inv)
    (s : Cocone F)
    (eY : s.pt ≅ (Etale.cohomology AddCommGrpCat.{u + 1} c.pt n).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapDerivedCategory.obj K.obj))
    (hs : ∀ a : Over i, s.ι.app (op a) =
      (e a).hom ≫
      (Etale.cohomology AddCommGrpCat.{u + 1} (D.obj a.left) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          (c.π.app a.left)).unit.app
            ((Etale.upperStar AddCommGrpCat.{u + 1} (D.map a.hom)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{u + 1} (c.π.app a.left)).hom.app
            ((Etale.upperStar AddCommGrpCat.{u + 1} (c.π.app a.left)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{u + 1} (D.map a.hom)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology AddCommGrpCat.{u + 1} c.pt n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{u + 1} (c.π.app a.left) (D.map a.hom)
            (c.π.app i) (c.w a.hom).symm) ≪≫
          Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{u + 1} (D.map a.hom))
            (Etale.upperStar AddCommGrpCat.{u + 1} (c.π.app a.left))).inv.app K.obj) ≫
      eY.inv) : IsIso (colimit.desc F s ≫ eY.hom) := by
  sorry

end AlgebraicGeometry
