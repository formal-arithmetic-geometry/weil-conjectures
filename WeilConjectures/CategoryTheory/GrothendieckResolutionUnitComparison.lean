/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckComposablePair
import WeilConjectures.CategoryTheory.CanonicalResolutionHomologyComparison
import WeilConjectures.CategoryTheory.CanonicalResolutionCompositeUnitComparison

/-! # Resolution comparisons and the composite derived unit

Source: Stacks Project, derived.tex, Tags 015M and 015N.
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The prescribed resolution identifies both ordinary derived homology and
composite derived homology with the complexes used to represent them. This assertion
compares the derived units and resolution isomorphisms; it involves no edge map.
Source: Stacks Project, derived.tex, Tags 015M and 015N. -/
theorem exists_grothendieck_resolution_unit_comparison
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (X : A) (I : InjectiveResolution X) (n : ℕ) :
    let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let L : CochainComplex.Plus B := ⟨K.extend ComplexShape.embeddingUpNat, 0,
      inferInstance⟩
    ∃ e : F.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≅ DerivedCategory.Plus.Q.obj L,
      (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso X n).hom ≫
          (I.isoRightDerivedObj F n).hom =
        (DerivedCategory.Plus.homologyFunctor B n).map e.hom ≫
          (DerivedCategory.Plus.homologyFunctorObjQIso L n).hom ≫
          (K.extendHomologyIso ComplexShape.embeddingUpNat
            (rfl : (n : ℤ) = n)).hom ∧
      (I.isoRightDerivedObj (F ⋙ G) n).inv ≫
          (F.grothendieckSpectralObjectHBotTopIso G hFG n).inv.app X ≫
          (DerivedCategory.Plus.homologyFunctor C n).map
            (G.rightDerivedFunctorPlus.map e.hom) =
        (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendHomologyIso
          ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).inv ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.mapExtendIso K ComplexShape.embeddingUpNat G).inv (n : ℤ) ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso
          (G.mapCochainComplexPlus.obj L) n).inv ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          (G.rightDerivedFunctorPlusUnit.app L) := by
  dsimp
  refine ⟨canonicalResolutionDerivedIso F I, ?_, ?_⟩
  · exact resolution_homology_transport F X I n
  · exact resolution_composite_unit_transport F G hFG X I n

end CategoryTheory
