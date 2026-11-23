/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.RightDerivedSingleDegreeComparison
import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
import WeilConjectures.CategoryTheory.RightDerivedCanonicalSingleUnitShift

@[expose] public section

universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]

/-- The canonical derived unit on a literal single complex in degree n.
Source: Stacks Project, Tag 015J. -/
theorem rightDerivedFunctorPlusUnit_canonical_single (X : B) (n : ℕ) :
    let S : CochainComplex.Plus B :=
      ⟨(CochainComplex.singleFunctor B (n : ℤ)).obj X, n, inferInstance⟩
    let e : (DerivedCategory.Plus.singleFunctor B n).obj X ≅
        DerivedCategory.Plus.Q.obj S :=
      DerivedCategory.Plus.ι.preimageIso
        ((DerivedCategory.singleFunctorIsoCompQ B n).app X)
    let GS := G.mapCochainComplexPlus.obj S
    GS.obj.homologyπ n ≫ (DerivedCategory.Plus.homologyFunctorObjQIso GS n).inv ≫
      (DerivedCategory.Plus.homologyFunctor C n).map
        (G.rightDerivedFunctorPlusUnit.app S) ≫
      (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlus.map e.inv) ≫
      (G.rightDerivedSingleDegreeComparison n).hom.app X =
    GS.obj.iCycles n ≫
      G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n X).hom := by
  have h := G.rightDerivedFunctorPlusUnit_canonical_single_shift X n
  dsimp only at h ⊢
  dsimp only [rightDerivedSingleDegreeComparison, Iso.trans_hom, NatTrans.comp_app]
  simp only [Iso.trans_hom, NatTrans.comp_app, ← Category.assoc] at h ⊢
  rw [h]
  simp only [Category.assoc]
  rw [← Category.assoc (G.rightDerivedPlusSingleUnitHomology X),
    rightDerivedPlusSingleUnitHomology_comp_comparison,
    rightDerivedZeroIsoSelf_inv_hom_id_app, Category.comp_id]

end CategoryTheory.Functor
