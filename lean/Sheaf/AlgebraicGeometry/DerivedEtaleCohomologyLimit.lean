/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Filtered.Basic
import Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Derived étale cohomology over an inverse limit

Source: literature/stacks-project/etale-cohomology.tex, Lemma Tag 0GIT
(blueprint: lem-weil-pbc-derived-etale-cohomology-limit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The projection pullbacks exhibit the derived étale cohomology of the limit as the
filtered colimit of the stage cohomology groups, with arbitrary abelian coefficients.
Source: Stacks Project, Étale Cohomology, Tag 0GIT
(blueprint: lem-weil-pbc-derived-etale-cohomology-limit).

The diagram and cocone are presented up to object isomorphisms `e` and `eY`.
Their maps are specified explicitly: apply derived global sections to the derived
adjunction unit, use the Leray isomorphism, then identify the iterated inverse image
with the inverse image along the composite. Thus these are the canonical pullback maps.

Proof: represent the bounded-below object by a complex zero below some integer `a`,
using good truncation (def-weil-abstract-derived-category and
 def-weil-pbc-bounded-derived-subcategories). Pull it back termwise at each stage and
at the limit (def-weil-pbc-derived-inverse-image). The composition identifications
(lem-weil-pbc-inverse-image-composition) make the pulled-back diagram on the limit
constant, so its termwise filtered colimit is the limit pullback
(lem-weil-pbc-colimit-constant-connected-diagram). Apply continuity for uniformly
bounded-below complex systems (lem-weil-pbc-etale-cohomology-limit-complex-systems,
Stacks 0EZM). Its maps are the projection pullbacks. Identify their cohomology with
cohomology of derived global sections (def-weil-pbc-etale-cohomology); the resulting
canonical cocone is a colimit in every integer degree. -/
theorem derivedEtaleCohomology_limit
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (T : Scheme.{u}) (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (t : D ⟶ (Functor.const I).obj T) (p : c.pt ⟶ T)
    (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) (F : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (e : ∀ i : I, F.obj (op i) ≅
      (Etale.cohomology AddCommGrpCat.{u + 1} (D.obj i) n).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} (t.app i)).mapDerivedCategory.obj K.obj))
    (hm : ∀ {i j : I} (f : i ⟶ j), F.map f.op =
      (e j).hom ≫
      (Etale.cohomology AddCommGrpCat.{u + 1} (D.obj j) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          (D.map f)).unit.app
            ((Etale.upperStar AddCommGrpCat.{u + 1} (t.app j)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{u + 1} (D.map f)).hom.app
            ((Etale.upperStar AddCommGrpCat.{u + 1} (D.map f)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{u + 1} (t.app j)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology AddCommGrpCat.{u + 1} (D.obj i) n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{u + 1} (D.map f) (t.app j)
            (t.app i) ((Category.comp_id (t.app i)).symm.trans (t.naturality f).symm)) ≪≫
          Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{u + 1} (t.app j))
            (Etale.upperStar AddCommGrpCat.{u + 1} (D.map f))).inv.app K.obj) ≫
      (e i).inv)
    (s : Cocone F)
    (eY : s.pt ≅ (Etale.cohomology AddCommGrpCat.{u + 1} c.pt n).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} p).mapDerivedCategory.obj K.obj))
    (hs : ∀ i : I, s.ι.app (op i) =
      (e i).hom ≫
      (Etale.cohomology AddCommGrpCat.{u + 1} (D.obj i) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          (c.π.app i)).unit.app
            ((Etale.upperStar AddCommGrpCat.{u + 1} (t.app i)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{u + 1} (c.π.app i)).hom.app
            ((Etale.upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{u + 1} (t.app i)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology AddCommGrpCat.{u + 1} c.pt n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{u + 1} (c.π.app i) (t.app i) p
            (hp i).symm) ≪≫
          Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{u + 1} (t.app i))
            (Etale.upperStar AddCommGrpCat.{u + 1} (c.π.app i))).inv.app K.obj) ≫
      eY.inv) : Nonempty (IsColimit s) := by
  sorry

end AlgebraicGeometry
