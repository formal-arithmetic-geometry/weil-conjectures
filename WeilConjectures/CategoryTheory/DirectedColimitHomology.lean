/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Homology commutes with directed colimits of abelian-group complexes.

Source: Stacks Project, Tag 00DB.
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

set_option backward.isDefEq.respectTransparency false in
/-- Tag 00DB, expressed as preservation of colimits by short-complex homology.
The evaluation and colimit homology isomorphisms commute with the cocone legs by
`ShortComplex.homologyMap_mapNatTrans`. -/
private theorem shortComplexHomologyPreserves
    {I : Type u} [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (ShortComplex.homologyFunctor AddCommGrpCat.{u}) := by
  classical
  refine ⟨fun {F} ↦ ?_⟩
  let S := (ShortComplex.functorEquivalence I AddCommGrpCat.{u}).inverse.obj F
  let e : S.homology ≅ F ⋙ ShortComplex.homologyFunctor AddCommGrpCat.{u} :=
    NatIso.ofComponents
      (fun i ↦ (S.mapHomologyIso ((evaluation I AddCommGrpCat.{u}).obj i)).symm)
      (by
        intro i j f
        have h := S.homologyMap_mapNatTrans ((evaluation I AddCommGrpCat.{u}).map f)
        change ShortComplex.homologyMap (F.map f) = _ at h
        change S.homology.map f ≫
          (S.mapHomologyIso ((evaluation I AddCommGrpCat.{u}).obj j)).inv =
          (S.mapHomologyIso ((evaluation I AddCommGrpCat.{u}).obj i)).inv ≫
            ShortComplex.homologyMap (F.map f)
        rw [h]
        simp)
  let a : colimit (F ⋙ ShortComplex.homologyFunctor AddCommGrpCat.{u}) ≅
      (ShortComplex.colimitCocone F).pt.homology :=
    (colim.mapIso e).symm ≪≫ (S.mapHomologyIso colim).symm
  refine preservesColimit_of_preserves_colimit_cocone
    (ShortComplex.isColimitColimitCocone F) ?_
  apply IsColimit.ofIsoColimit (colimit.isColimit _)
  refine Cocone.ext a ?_
  intro i
  have h := S.homologyMap_mapNatTrans (colim.ι (C := AddCommGrpCat.{u}) i)
  change ShortComplex.homologyMap ((ShortComplex.colimitCocone F).ι.app i) = _ at h
  change colimit.ι _ i ≫ a.hom =
    ShortComplex.homologyMap ((ShortComplex.colimitCocone F).ι.app i)
  rw [h]
  simp [a, e]

/-- Homology preserves directed colimits, including the empty colimit.

Source: Stacks Project, Tag 00DB (directed-colimit exactness). -/
theorem directed_colimit_homology
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (c : ComplexShape (ℤ × ℤ)) (pq : ℤ × ℤ) :
    PreservesColimitsOfShape I (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} c pq) := by
  classical
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} c pq
  by_cases hI : Nonempty I
  · have : Nonempty I := hI
    have : PreservesColimitsOfShape I
        (ShortComplex.homologyFunctor AddCommGrpCat.{u}) := shortComplexHomologyPreserves
    have : PreservesColimitsOfShape I
        (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} c pq) := by
      refine ⟨fun {F} ↦ ⟨fun {s} hs ↦ ⟨?_⟩⟩⟩
      apply ShortComplex.isColimitOfIsColimitπ
      · exact isColimitOfPreserves (HomologicalComplex.eval _ _ (c.prev pq)) hs
      · exact isColimitOfPreserves (HomologicalComplex.eval _ _ pq) hs
      · exact isColimitOfPreserves (HomologicalComplex.eval _ _ (c.next pq)) hs
    exact preservesColimitsOfShape_of_natIso
      (HomologicalComplex.homologyFunctorIso AddCommGrpCat.{u} c pq).symm
  · have : IsEmpty I := not_nonempty_iff.mp hI
    have : PreservesColimit (Functor.empty.{0} _) H :=
      Functor.preservesInitialObject_of_preservesZeroMorphisms H
    have : PreservesColimitsOfShape (Discrete PEmpty.{1}) H :=
      preservesColimitsOfShape_pempty_of_preservesInitial H
    exact preservesColimitsOfShape_of_equiv
      (equivalenceOfIsEmpty (Discrete PEmpty.{1}) I) H

end CategoryTheory
